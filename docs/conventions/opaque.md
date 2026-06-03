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

**The kernel bridges *construct* sites automatically.** Opacity blocks
δ-unfolding during general `weakHeadNormalForm`, so goal/term *shape* is
preserved — but the kernel's definitional-equality check has an
opacity-tolerant fallback (`unfoldOpaqueHeadOnce` in `kernel.cpp`): when a
comparison would otherwise fail and one side is headed by an opaque constant,
it retries with that head made transparent, a single local unfold. So a proof
whose type is `Foo`'s *unfolded* form, checked against an expected `Foo(…)`
type, type-checks **without any `unfold`** — the kernel sees through the
opaque wrapper at the final equality step only. This is what makes the bulk
of the old construct-site `unfold`s unnecessary.

**`unfold Foo in <body>`** remains the escape hatch for the cases the defeq
bridge can't reach — sites where the *elaborator* (not just the kernel's
equality check) must see `Foo`'s body:
- **destruct** — consuming a `Foo`-typed value as its unfolded form
  (`cases x refining aFoo`, `obtain ⟨…⟩ from aFoo`, applying it as
  `aFoo(arg)`): the elaborator needs the unfolded *Pi/inductive* head, which
  general WHNF won't expose.
- **`claim by substituting` on an opaque recursive step** — the rewrite needs
  the unfolded body visible to find its target (e.g. `divide_step`'s inner
  `cases monus(p, n)`).
- structured intro under an opaque expected type (a `witness …`/block proof
  driven by `Foo`'s unfolded `∀/∃` shape).

It temporarily flips `Foo` to transparent while elaborating `<body>`.

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
`Natural.power`, `Real.IsNonneg`, `Rational.IsNonneg`.

### A second motivation: a `Quotient.lift` abstraction boundary

`Real.IsNonneg` and `Rational.IsNonneg` are opaque for a different
reason than the recursive functions above — they are **not** recursive,
they are `Quotient.lift(predicate_at_representative, respect, x)`
wrappers. The order relations fold on top of them:
`Real.LessOrEqual(x, z) := Real.IsNonneg(z - x)`.

The problem opacity solves: WHNF on a goal like `x ≤ z` blew straight
through `LessOrEqual → IsNonneg → Quotient.lift`, landing in
`Quotient.lift(...)` form. The characterising lemmas (`IsNonneg.add`,
`IsNonneg.multiply`, `from_natural_is_nonneg`, …) are all stated in
`IsNonneg(…)` form, so the auto-prover's `contextFactMatch` couldn't
line a `Quotient.lift`-shaped goal up against them, and the resistant
order transports needed a hand-written `rewrite(eq, IsNonneg.add(…))`.

Marking `IsNonneg` opaque makes WHNF stop at `IsNonneg(z - x)` — exactly
the form the characterising lemmas use. The transports then convert to
`claim IsNonneg(diff) by substituting eq` (see
`calc-and-rewrite.md`); the auto-prover discharges the rewritten goal
from the characterising lemma plus the order hypotheses in context. It
also stops the `Quotient.lift`/`IsEventuallyNonneg` implementation from
leaking into every order proof.

Classify each failure after marking such a wrapper opaque as **construct**
or **destruct**:

- **construct** — the body builds the rep-level form (`(ε) ↦ witness …`
  for Real, an `Integer.IsNonneg(n)` leaf for Rational) where an
  `IsNonneg(…)` is expected. **No `unfold` needed** when the body is a
  bottom-up-inferable term (a lemma application, `reflexivity`, a `rewrite`,
  a `cases` ascribed to the `IsNonneg(…)` form): the kernel's defeq bridge
  matches the rep-level actual type against the opaque expected type
  directly. Only a *structured* construct — a `witness …`/block proof that
  needs `IsNonneg`'s unfolded `∀/∃` shape to drive the intros — still wraps
  in `unfold Real.IsNonneg in (…)`.
- **destruct** — the body consumes an `IsNonneg` value as if it were the
  rep form: `cases x refining anIsNonneg`, `obtain ⟨…⟩ from anIsNonneg`,
  applying it as `(ε)(εpos)`, or handing it to a lemma that wants the
  unfolded type. Symptom: `function is not of Pi type` / `argument type
  does not match Pi domain` with actual type `IsNonneg (…)`. These **keep**
  `unfold Real.IsNonneg in (…)` — the elaborator needs the unfolded Pi/
  inductive head, which the kernel's equality-only bridge does not provide.

Pure **uses** (transitivity/antisymmetry citations, `cases B refining
hyp` pass-throughs, the `claim by cases` linearity splits) operate on
the `IsNonneg` arguments and lemmas, not the unfolded body — they keep
working **unchanged**. Only construct/destruct sites need `unfold`.

The `by substituting` payoff has one wrinkle: substituting only fires on
a goal whose head it can see, so state the claim in the **`IsNonneg(diff)`
form** (defeq to the `≤` goal but syntactically exposing `diff`) and give
the equation as `(ring : <expanded> = <diff>)` with the subtraction
written the same way on both sides. `claim x ≤ z by substituting …`
reports `0 occurrences` because the `≤`/`LessOrEqual` head is never
unfolded for the match.

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
   equation. A `reflexivity`-bodied equation needs **no `unfold`**: the
   kernel's defeq bridge unfolds `Foo` once to match the two sides (the
   declared `Foo(constructor args)` reduces, the body's `reflexivity` target
   is its value). Only an equation that itself case-splits on a hypothesis
   (`claim by substituting …`, `Equality.transport_proposition(…)`) keeps
   `unfold Foo in …`, since the rewrite must see `Foo`'s unfolded body.
   Example for `Natural.monus` (all three are now `unfold`-free):
   ```math
   theorem Natural.monus_zero_left (b : Natural)
           : Natural.monus(0, b) = 0 :=
     reflexivity(Natural, 0)
   theorem Natural.monus_succ_zero (k : Natural)
           : Natural.monus(successor(k), 0) = successor(k) :=
     reflexivity(Natural, successor(k))
   theorem Natural.monus_succ_succ (k j : Natural)
           : Natural.monus(successor(k), successor(j))
             = Natural.monus(k, j) :=
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

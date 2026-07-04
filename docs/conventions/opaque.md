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

**`opaque` is HARD: an opaque head is never implicitly unfolded, not even at a
demand point.** Opacity blocks δ-unfolding during general `weakHeadNormalForm`
(so goal/term *shape* is preserved for `rewrite` and the auto-prover's
syntactic matchers), AND it refuses the demand-point force-unfold retries — the
kernel defeq leaf, the inferType-application bridge, the elaborator's
deep-WHNF (`by substituting`), cases-on-expression, and tuple/lambda/Pi intro
all leave an opaque head stuck. `isHardOpaqueConstant` (kernel.cpp) returns
true for every opaque constant; the two bridge entry points
(`unfoldOpaqueHeadOnce`, `Elaborator::opaqueHeadDefinition`) bail out on it.
(Earlier — the "WS2 soft bridges" — these retries *did* fire, gated per-name by
the `MATH_HARD_OPAQUE` env var during the predictability experiment; that gate
is retired and hard is now the standing behaviour.)

So the only way to see through an opaque head is to ask for it explicitly:

- **`<hint> by … unfolding Foo`** — the PREFERRED form. `unfolding Foo[, …]` is
  a postfix `by`-hint modifier (parallel to `recalling`) that discharges the
  step with `Foo` transparent. It piles onto any hint and stands alone:
  `done by unfolding Foo` (auto-prover), `done by <lemma> unfolding Foo`,
  `claim P by substituting eq unfolding Foo`, `… = … by unfolding Foo` (calc
  step). It reads "*I claim this, as you can check by unfolding the definition
  of Foo*" — the claimed proposition stays on the page; the unfold is just the
  cited reason. (Contrast `unfold Foo in <body>`, which silently reshapes the
  goal you then write `<body>` against — that hidden-goal style is on the CIC
  naughty list.)
- **`unfold Foo in <body>`** (the wrapper) survives only as an escape hatch for
  a body that can't sit after `by`: a multi-statement `{ … }` block, a
  multi-arm `cases`, a `calc`, or a mid-expression term use
  (`(unfold Foo in h)(args)`). Prefer the `by … unfolding` form everywhere else.
- **Boundary / characterising lemmas** — the preferred route. Prove the
  fold/unfold *once* in a tiny named lemma (whose body is the `unfold`), and
  have every consumer cite the name. The opacity is pierced in one place; no
  `Quotient.lift` / unfolded view leaks into the consumers. See the IsNonneg
  boundary pair below.

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

Opaque **types** (sealed quotients, reasoned about only through a boundary API —
see the `Integer` / `Rational` discussion below): `Integer`, `IntegerEquivalent`,
`Rational`.

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

**The boundary lemmas.** Each opaque `IsNonneg` publishes a fold/destruct pair,
proved once with `unfold`, that consumers cite by name:

```math
-- Rational/order.math — denominators are now arbitrary nonzero Integers, so the
-- sign witness is `Integer.IsNonneg(n · d)` (for d > 0 this is n ≥ 0; for d < 0
-- it flips, exactly as the fraction's value demands).
theorem Rational.IsNonneg.of_numerator_denominator
        (n d : Integer) (denominatorNonzero : ¬(d = Integer.zero))
        (productIsNonneg : Integer.IsNonneg(n * d))
        : Rational.IsNonneg(Rational.fraction(n, d, denominatorNonzero)) :=
  unfold Rational.IsNonneg in productIsNonneg
theorem Rational.IsNonneg.numerator_denominator
        (n d : Integer) (denominatorNonzero : ¬(d = Integer.zero))
        (fractionIsNonneg : Rational.IsNonneg(Rational.fraction(n, d, denominatorNonzero)))
        : Integer.IsNonneg(n * d) :=
  unfold Rational.IsNonneg in fractionIsNonneg
```

`Real.IsNonneg` has the analogous `of_eventually_nonneg` / `eventually_nonneg`
pair over `CauchyRationalSequence.IsEventuallyNonneg`. The consumer rule:

- **destruct** — route through `.numerator_denominator` / `.eventually_nonneg`.
  After `cases x { | rep => … }` (h refines automatically), `h : IsNonneg(mk rep)`; feed it to
  the destructor to recover the rep-level fact (`Integer.IsNonneg(n · d)`). Sites
  that *apply* an IsNonneg value as the `∀ε∃N` form use
  `(unfold Real.IsNonneg in h)(…)`.
- **literal / nameable-rep construct** — cite `.of_numerator_denominator` /
  `.of_eventually_nonneg`. `by Rational.IsNonneg.of_numerator_denominator` even
  auto-discharges the `Integer.IsNonneg(n · d)` premise when the auto-prover can
  find it (e.g. `Integer.zero_is_nonneg`).
- **arithmetic-result or constant construct** (sums, products, `Real.zero`, the
  Real `*_at_make` ε/δ lemmas, triangle, the supremum bisection bounds) — the
  reduced fraction/sequence is awkward to spell, so keep a goal-side
  `unfold X in <rep-level proof>`. This is the at-representatives pattern; the
  `unfold` is local to that one helper.

Pure **uses** (transitivity/antisymmetry citations, `cases B` hypothesis
pass-throughs, the `claim by cases` linearity splits) operate on the
`IsNonneg` *arguments* and lemmas, not the unfolded body — they need nothing
special, since `LessOrEqual`/`LessThan` are transparent and reduce to
`IsNonneg(diff)` without touching the opaque head.

The `by substituting` idiom (for the order transports) has one wrinkle:
substituting only fires on a goal whose head it can see, so state the claim in
the **`IsNonneg(diff)` form** (defeq to the `≤` goal but syntactically exposing
`diff`) and give the equation as `(ring : <expanded> = <diff>)` with the
subtraction written the same way on both sides. `claim x ≤ z by substituting …`
reports `0 occurrences` because the `≤`/`LessOrEqual` head, though transparent,
isn't what carries `diff` for the match.

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
   equation, each body an `unfold Foo in <reflexivity / substituting>`. The
   `unfold` is what lets the declared `Foo(constructor args)` reduce to the
   body's value; outside it the head stays stuck. An equation that case-splits
   on a hypothesis pairs `unfold` with `claim by substituting …`, which then
   sees `Foo`'s inner `cases` while keeping the substituted endpoint's head
   intact. Example for `Natural.monus`:
   ```math
   theorem Natural.monus_zero_left (b : Natural)
           : Natural.monus(0, b) = 0 :=
     done by unfolding Natural.monus
   theorem Natural.monus_succ_zero (k : Natural)
           : Natural.monus(successor(k), 0) = successor(k) :=
     done by unfolding Natural.monus
   theorem Natural.monus_succ_succ (k j : Natural)
           : Natural.monus(successor(k), successor(j))
             = Natural.monus(k, j) :=
     done by unfolding Natural.monus
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

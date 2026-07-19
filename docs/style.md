# Style guide

The standard is simple: a proof should read like mathematics, with the
kernel checking it. The files in `scripts/clean_manifest.txt` are the best
current examples.

## Start from the public interface

Read `library/<Area>/README.md` before using an area. Prefer its named
definitions and theorems to representation details.

Outside `Natural/`, use `ℕ`, numerals, and arithmetic. Do not use
`zero`, `successor`, `Natural.Raw`, constructor patterns, or the raw
recursor. Write `n + 1` or `1 + n` and use equation-shaped cases and
induction.

Do not unfold an opaque abstraction in consumer code. If its public
interface is missing a useful characterization, add that boundary theorem.

## State the mathematics

Use a relation chain when the argument is transitivity, rewriting, or
calculation:

```math
first
   = middle by reason
   ≤ last
```

Inside a proof block, state intermediate propositions directly:

```math
P;
Q by theoremName;
```

Name a fact with `as name` only when later text explicitly uses the name.
Anonymous facts remain available by their propositions.

## Let inference remove plumbing

Try a by-less fact or chain step first. The prover uses local hypotheses,
`automatic` declarations, and its built-in equality, order, sign, and
algebra reasoning.

When help is needed, cite the operative theorem without positional proof
arguments:

```math
desiredFact by ImportantTheorem;
```

Avoid:

```math
ImportantTheorem(a, b, premise)
```

unless an argument is genuine mathematical data that cannot be inferred.

For commutative-ring identities, try `ring` first. For field identities
with division, try `field(nonzeroFacts...)`.

## Use the proof structure that matches the argument

- Universal statement: `take`.
- Implication: `suppose`.
- Existential introduction: `witness`.
- Existential elimination: `choose`.
- Inductive argument: `by induction`.
- Structural alternatives: equation-shaped `done by cases`.
- Classical condition: `done by cases { case P: ... otherwise: ... }`.
- Conditional data: `if P then ... else ...`.
- Contradiction: `suppose ... for contradiction` or a directly stated
  impossible fact followed by `done`.

Raw scrutinee pattern splitting is not part of the proof language. Use the
equation-shaped alternatives, induction, or the public data-destructuring
form for the type.

## Keep logical connectives mathematical

Do not expose the tuple encoding of `∧` and `∃`.

- Build `A ∧ B` by establishing `A`, then `B`, then `done`.
- Use a conjunction by stating the needed leg.
- Build `∃ x. P(x)` with `witness`.
- Use it with `choose`.
- Prove `A ∨ B` by establishing the true side and closing.
- Eliminate a disjunction with `done by cases`.

Tuple syntax remains appropriate for genuine data records.

## Separate construction from use

A clean abstraction file normally has:

1. a representation or construction;
2. characterizing boundary theorems;
3. representation-level proofs kept close to the construction;
4. thin public adapters;
5. consumer theorems written entirely through the public interface.

Do not let quotient, subtype, raw-constructor, or transport machinery leak
into ordinary mathematical results. The worked patterns — boundary-lemma
layering, pattern-matching at constructor representatives for
Quotient-lifted proofs, and when an auxiliary sequence definition is a
red flag — are in `conventions/quotients.md` ("Layering and
machinery quarantine").

The sections below are the worked depth: the preferred split and
induction forms, the raw-CIC tells, the statement-level sugar, when
to hint, the machinery-quarantine patterns, and the polishing
workflow. Read them before writing or polishing proofs.

## Prefer equation-shaped `by cases` / `by induction` over pattern-match

Mathematicians don't write proofs as separated equation cases at the
outer-syntax level — they write a body that opens with "by cases" or
"by induction on n" and then handles each shape. The proof-level split
is **equation-shaped**: each arm states what the scrutinee *equals*,
with `for some` binding the constructor arguments.

```math
-- Non-recursive case split:
theorem Natural.foo (n : ℕ) : P(n) :=
  done by cases {
    case n = 0:                    baseProof
    case n = 1 + k for some k:     stepProof
  }

-- Recursive (k's IH needed in the step arm):
theorem Natural.foo (n : ℕ) : P(n) :=
  by induction on n with IH {
    case n = 0:                    baseProof
    case n = 1 + k for some k:     stepProof   -- IH : P(k)
  }
```

Each arm's equation refines the goal (and the hypotheses that mention
the scrutinee); exhaustiveness discharges through the type's coverage
theorem. Constructor spellings stay behind the `Natural/` boundary
(see `conventions/numerals-and-naming.md`).

Pattern-match **definitions** (`definition f | 0 => … | 1 + k => …`)
remain the tool for direct recursion that doesn't fit `by induction`'s
motive shape — for example when the conclusion is universally
quantified over a parameter that the IH must be polymorphic over
(`Natural.decides_equality` recursing on `a` while the IH must work
for all `b`). Use equation-shaped `by cases`/`by induction` by
default; reach for a pattern-match definition only when the recursion
really demands it.

### Branch on a *condition*, not a constructor

A branch in a proof is an equation-shaped split (above), a condition
split, or data-dispatch pushed into a helper definition:

- **value-level, a decidable condition** (in a `definition`):
  `if i < m then a else b` — the classical conditional (see
  `reference.md`); reason about it with `Logic.if_positive` /
  `Logic.if_negative`. A generic value type (`{A : Type(0)}`) sidesteps
  the "cases motive must end in a Sort" quirk a projection return type
  (`Field.carrier(f)`) would trigger.
- **proof-level, a decidable condition**:
  `by cases { case i < m as h: … otherwise as h2: … }` — the decidable
  split (`import axioms` for `otherwise`).
- **dispatching on a computed *data* value** (not a `Prop` condition —
  e.g. a `StrictComparison`, or `monus(a,b)`'s zero-or-not shape):
  push the destructure into a **helper that pattern-matches its
  argument** (the pattern-match-*definition* form `definition f | Ctor(x)
  => …`, whose scrutinee IS a bound parameter). The library does exactly this —
  `Natural.compare_strict_shift` matches the `StrictComparison` passed
  to it.

**Even a branch that needs the decision PROOF** (building a dependent
value like a `NaturalsBelow` witness, `NaturalsBelow.sum_out_of`) does
NOT need `cases`: `if` binds the proof anonymously but leaves it in
scope, so restate the condition as a stated fact in the branch block to
recover a named handle —

```math
if i < 1 + m
then { i < 1 + m as h;  NaturalsBelow.make(i, h) }   -- h : i < 1 + m
else { m ≤ i by …;      … }                          -- from ¬(i < 1 + m)
```

(The restatement line is mild friction; an `if P as h then …` sugar that
binds the proof directly is a candidate, not yet built.)

## Case-split with retained equation: state it in the arm

To case-split on an expression and keep the equation between the
expression and the matched form on the page, use the equation-shaped
by-cases split:

```math
done by cases {
  case Integer.absolute_value_natural(x) = 0 as refinedEquation: …
  case Integer.absolute_value_natural(x) = 1 + k
         for some (k : ℕ) as refinedEquation: …
}
```

Each arm's equation is an ordinary stated hypothesis — citable,
statement-addressable, and transported by the prover — and
exhaustiveness discharges through the type's coverage lemma.

## Classical case-splits: `by cases { case P: … otherwise: … }`

The canonical form for "P or not P" reasoning in proofs. `otherwise` is always
last; its hypothesis is ¬(the stated cases), and exhaustiveness is
excluded middle by construction — it cannot fail to cover.

```math
done by cases {
  case x = Real.zero: …           -- x = 0 in scope (anonymous; `as h` names it)
  otherwise as xNotZero: …        -- ¬(x = 0) in scope
}
```

**When the goal must REDUCE a conditional definition** (`min(a, b)`,
`List.filter`, a bisection step — anything defined by `if P then a
else b` or a `Decidable`-parametrized helper), do NOT re-decide: a
propositional split cannot ι-reduce the `classical_decidable(P)` term
buried in the definition. Reason through the definition's
**characterizing equations** instead, which are one-liners over the
generic conditional lemmas `Logic.if_positive` / `Logic.if_negative`:

```math
theorem Rational.minimum_eq_left (a b : Rational) (aLeqB : a ≤ b)
        : min(a, b) = a :=
  by Logic.if_positive

-- and in a consumer:
done by cases {
  case a ≤ b: {
      min(a, b) = a by Rational.minimum_eq_left;
      done by substitution
    }
  otherwise: …
}
```

Every conditional definition publishes its characterizing equations
right below itself (`minimum_eq_left/right`,
`filter_prepend_positive/negative`, `bisectionStep_eq_of_[not_]upper_bound`
plus the endpoint recurrences in Real/supremum.math); consumers never
case-analyze the classical decision.

> **Import:** `if P then a else b` desugars to
> `cases Logic.classical_decidable(P)`, a **theorem** in
> `Natural.classical_decidable` (derived from excluded middle +
> `Logic.the`). A module using `if` must reach that file; an `unknown
> identifier 'Logic.classical_decidable'` means you need
> `import Natural.classical_decidable`.

## Introducing a disjunction — state the side, skip `Or.introduce*`

To prove an `A ∨ B` goal you don't have to name `Or.introduceLeft` /
`Or.introduceRight`. Two by-less options, in preference order:

- **Bare `done`** — let the auto-prover prove the whole disjunction: it
  tries `A`, then `B`, from context and wraps the matching constructor.
  Best when the winning side is *cheap* for the prover (a hypothesis,
  reflexivity, a short transitivity chain). It will also close sides that
  need a library search, but that can be slow — don't lean on it for a
  disjunct that needs a specific cited lemma plus algebra.
- **State the side directly** — give a proof whose type *is* one disjunct
  (a hypothesis, a relation chain, a lemma application) and the
  **disjunction-injection coercion** wraps the right constructor. This is
  a targeted, search-free coercion (it matches the proof's type against
  each disjunct up to definitional equality), so it's the right tool when
  the side needs real work the prover wouldn't find:
  ```math
  done by cases {
    case quotient = 0:
        n = d * quotient = d * 0 = 0
    case ∃ (qm1 : ℕ). quotient = 1 + qm1 as quotientIsPositive: {
        choose qm1 such that quotient = 1 + qm1 from quotientIsPositive;
        d ≤ d + d * qm1
              = d * (1 + qm1)
              = d * quotient
              = n
      }
  }
  ```
  (`Natural.divides_less_or_equal_or_zero`, quoted.) Both arms read as
  the mathematics ("n is 0", "n ≥ d") with the `Or` wrapper inferred —
  each arm's final chain lands on one disjunct and the injection
  coercion wraps it. Spell out `Or.introduceLeft` / `Or.introduceRight` only when the
  proof term is itself ambiguous about which side it proves.

## Write proofs that read like math

The overriding goal is that a proof reads like what a mathematician
would write in a textbook, with the kernel doing the typechecking. A
human should be able to scan the proof and follow the argument
without parsing CIC bureaucracy. The optimization target is
**readability**, not terseness.

Concretely:

- **No abbreviations.** Both in identifiers (see `conventions/numerals-and-naming.md` —
  `representative`, not `rep`, in declared names) and in
  binders within proofs. Verbosity that aids comprehension is a
  feature, not a cost — `halvedEpsilonPositive`, not `hep`.
- **Consider the ellipsis for reader-facing sums.** A statement a text
  writes term-by-term should be spelled that way:
  `(1 - r) * (r^0 + r^1 + ... + r^(n - 1)) = 1 - r^n`
  (`Real.geometric_series`). Inside relation chains keep the binder form
  (`Ring.Sum(r, (i) ↦ …, k)`) — the `Sum.*` lemma library speaks it —
  and write the ellipsis's edge terms unsimplified (`q[k ∸ 0]`, not
  `q[k]`): term-function inference is syntactic.

- **Math-like phrasing.** Compose the proof out of named
  mathematical steps. A reader should see "triangle inequality on
  (a − b) and b", "subtract |b| from both sides", "case split on
  the sign of (|a| − |b|)" — not a wall of `congruenceOf` /
  `transport_proposition` calls.

- **Length is fine if it's pedagogical.** Don't golf. A 40-line
  proof that explains each step in *named mathematical steps* is better
  than a 10-line proof that requires unwinding three nested
  `Quotient.lift` calls in your head to follow. But the explanation
  belongs in the proof code — a relation chain, named stated facts, `by`
  citations — not in a comment narrating what the code should already say
  (see the comment maxim below).

- **A relation chain is encouraged.** It mirrors how a mathematician
  writes an equation chain. Use it whenever you can name each
  intermediate form. Even a two-step chain is usually clearer than the
  equivalent `Equality.transitivity(...)`.

- **Bind a repeated long subexpression with `let`.** When the same verbose
  term (`Real.partialSum((j : Natural) ↦ s(m + j), m)`, `(x + y) / 2`) recurs,
  a `let secondSum : Real := …` / `let mean := …` collapses every line that
  uses it and makes the algebra legible — `(firstSum - secondSum) * (firstSum
  - secondSum)`, `mean < g → g * g < g * g`. This is the main lever for
  *un-chopping* a proof that has sprawled across many narrow lines (and pairs
  with the column-140 rule — merge first, bind to shorten). Mechanics and the
  `ring`/`field`-don't-unfold-`let` caveat live in `conventions/numerals-and-naming.md`.

- **A comment is an admission of defeat — make the *proof* carry the
  reasoning.** The aspiration (borrowed from good C++ practice) is that the
  proof reads like the mathematics on its own; a comment is a signal that a
  step wasn't saying enough. Triage every comment:
  - **A "what" comment is defeat.** `-- b divides 0 (every n divides 0)` over a
    bare `b ∣ 0;` puts the *reason* in prose, not code. Push it into the
    proof — `b ∣ 0 by Natural.divides_zero;` — and delete the comment.
    The lever is almost always a `by <named-lemma>`, a named stated fact, a
    relation-chain form, or `take`/`suppose`. (A stated fact stays bare
    only when a *tactic/computation* closes it — `ring`, defeq, the
    equality battery — where there is no lemma to name; see "don't
    justify routine computation".)
  - **A "why" comment may earn its place — for now, be lenient.** A genuinely
    non-derivable strategic choice ("recurse on the derivation, not the list";
    "scale both differences by `c` so the equality becomes one of classes") is
    the proof analog of a C++ comment explaining *why*, not *what*. Keep it to
    one line. As the surface language grows to express such intent directly,
    we tighten toward deleting these too.
  - **Kernel/elaborator mechanics are quarantined**, never mixed with the
    math: a marked `-- Implementation note:` aside, and only in the
    foundational plumbing files (`Logic/quotient`, `Equality/basics`, the
    Integer construction) — the analog of C++ that must comment a hardware
    erratum. The math-facing files aim for none.
  Re-read comments after restructuring a proof: a comment that still says "by
  `ring`" or "`inverse_right`" when the proof now does neither is worse than no
  comment.

- **Sequence-of-stated-facts style is encouraged.** When a proof has
  several distinct subgoals, write them as a sequence of `<type> by
  <proof> as <name>;` lines and then assemble the result from the named
  facts. This makes the structure of the argument legible and lets a
  reader skim the facts to see the shape before reading the inner proofs.

### What an ideal proof looks like — and the CIC tells that betray it

Write the proof a mathematician would, then make the kernel accept it —
NOT the other way around. The single biggest readability failure is
**raw-CIC style**: the proof typechecks but reads like type theory, not
mathematics. If you find yourself writing any of the following, stop and
reach for the math-like form instead:

- **`congruenceOf(…)` / `Equality.congruence(…)` — a raw-CIC stink,
  avoid by default.** "Apply `f` to both sides of `a = b`" is a
  one-step relation-chain whose justification is the inner equality:
  the elaborator's *diff-inferred congruence* wraps `f` automatically.
  The one documented fallback is a multi-occurrence motive (the same
  changed subterm at several positions at once) — see
  conventions/relation-chains.md.
  ```
  -- NOT: congruenceOf((x) ↦ Sum.left(A, B, x), valueEquality)
  Sum.left(A, B, recovered)
     = Sum.left(A, B, original)   by valueEquality        -- congruence inferred
  ```
  Caveat: after a `cases` (with its automatic hypothesis refinement) has
  already reduced the goal, the
  function application in the goal is *already* the reduced constructor
  form, while a freshly-written `f(g(x))` is *stuck* (neutral scrutinee).
  So **start the chain from the reduced form**, not from the original
  application.

- **`Equality.symmetry(…)` to flip an equation is usually unnecessary.**
  A chain `=` step's diff-inference already tries both orientations, so a
  *reversed* step needs only `by <lemma/hypothesis>` — `by bEquation`, not
  `by Equality.symmetry(bEquation)` — and the binder stays referenced. When
  the reversed equation is needed in *argument* position (no chain step to
  flip — e.g. feeding `equal_of_value` or another lemma), wrap it in a
  one-step `B = A by <proofOfAeqB>` rather than calling
  `Equality.symmetry`.

- **`NAME : a = c by <chain a = … = c>` is ceremony** — the chain's
  endpoints already *are* `a = c`, so the `NAME : <type> by` wrapper
  just restates it. Bind the chain's result directly:
  ```
  -- NOT: quotientLeK : n * q ≤ k by (n * q ≤ n * q + r = k);
  n * q ≤ n * q + r = k   as quotientLeK;
  ```
  Use `<chain> as NAME;` when the result is referenced later by name, and
  a bare `<chain>;` when it's only consumed by type-match (see
  conventions/relation-chains.md, "the bare chain statement forms"). And when the chain *is*
  the whole proof, it is the proof — write `:= <chain>` / return the
  chain, never `<goal> by <chain>`.

- **`Equality.transport_proposition(…)` to move a fact along an
  equation** — use a chain step or `by substituting <eq>` instead.

- **Raw `Subtype.make(Carrier, (k) ↦ …predicate…, value, proof)` at call
  sites** — when you carve a type out with a predicate (`Subtype`,
  `NaturalsBelow(n) := Subtype(Natural, k ↦ k < n)`, …), give it a small
  **element interface** up front and use *only* that: `Foo.make(value,
  proof)`, `Foo.value(e)`, a projection for the defining property, and an
  extensionality lemma `Foo.equal_of_value` (proof-irrelevance collapses
  the membership proofs, so equality reduces to value-equality). Then every
  downstream proof argues about *values*, never about the `Subtype`
  spelling. Writing the interface costs a dozen lines once and removes the
  CIC spelling from every theorem that follows.

- **An extensionality bridge applied to a lambda** —
  `CoordinateSpace.equal_of_pointwise((k : …) ↦ { … })`,
  `Function.extensionality(…, (x : …) ↦ …)` — is a raw-CIC tell: it
  spells "apply the lemma to the function k ↦ proof" where a
  mathematician writes "check it coordinatewise". State the pointwise
  fact, then close by the bridge, argument-free:
  ```
  take u : CoordinateSpace(f, n);
  take v : CoordinateSpace(f, n);
  ∀ (k : NaturalsBelow(n)). u(k) + v(k) = v(k) + u(k) by Field.add_commutative;
  done by CoordinateSpace.equal_of_pointwise
  ```
  The stated ∀-fact needs its `by` (the auto-prover does not
  ∀-introduce a bare fact): name the operative lemma when one instance
  carries it, otherwise `by { take k : …; <chain or done> }`. The same
  move reads top-down as `suffices ∀ (k : …). … by <bridge>; take k; …`
  (see reference.md) — prefer whichever the two criteria favor at the
  site: bottom-up is usually shorter when the coordinatewise fact is a
  one-liner; `suffices` keeps a genuinely multi-step coordinatewise
  chain at statement level instead of nested inside a `by { … }`.
  Keep the closing `done by <bridge>` even where the prover closes
  without it — how the pointwise fact yields the equality is the one
  step the reader must not have to guess.

- **Direct proof-lemma calls** — applying a `theorem` to positional
  arguments — are discouraged *entirely*, at every arity. Not just
  `LessOrEqual.transitive(a, b, c, p, q)` but also the one-argument
  `LessThan.weaken(proof)`: both invoke the lemma as a
  function instead of reading as mathematics. **State the fact and
  discharge it by name, argument-free**: `T by <Lemma>` (which binds
  `T` into context), or chain it via a relation chain,
  letting goal-driven inference + context-discharge fill the arguments (see
  structures-and-inference.md, "Citing a lemma by name"). Name the
  *operative result* (the insight), not the plumbing. (This is a proof
  citation rule only — value-level applications such as constructors,
  `ring`/list/arithmetic ops, and `witness … with …` data are fine.)
  - Do **not** try to shrink a direct call by making the lemma's leading
    data-args implicit: `Foo.bar(proof)` is still a direct call. The fix is
    `by Foo.bar`, not a shorter application.
  - **Recursion reads as induction.** A pattern-matched proof whose body
    recurses by a positional self-call (`Foo.bar(predecessor, …)`) hides the
    induction in a comment AND counts as a direct call. Write it
    `by induction on a with IH { case a = 0: … case a = 1 + p
    for some p: … }` instead: the hypothesis is the named local
    `IH`, cited argument-free like any fact (`done by IH`),
    so the recursion both reads as induction and is no longer a lemma call.
    Hypotheses whose types mention the inducted variable are generalised
    automatically (the IH then quantifies over them); write
    `generalizing b, c` only for induction loading — an IH the proof must
    apply at *different* values of extra binders. The shape
    (cancellation on the left, `a + b = a + c → b = c`):
    ```
    by induction on a with IH {
      case a = 0:
          equalityHypothesis
      case a = 1 + p for some p: {
          p + b = p + c;
          done by IH
        }
    }
    ```
    This also works for induction on a **derivation** (an indexed inductive
    `Prop`, e.g. a `≤` proof) — use the constructor names as cases; a
    hypothesis mentioning an index the induction varies is generalised
    automatically. The case bodies use the constructor's *destructured*
    index names, not the outer binders; `IH` (or `IH(<generalised-hyp>)`)
    is the named hypothesis.
  - **Closers.** `done` and `okay` are a bare restatement of the `goal`
    (the expected type). A bare `done`/`okay` discharges the goal by
    lookup; each also takes an optional `by <hint>`. `goal` itself is
    only the NAME of the type being proved — a type reference (`done by
    …`, `note goal : T`), NOT a standalone closer (`goal by …` is
    rejected; write `done by …` / `okay by …`). Keep an illuminating
    `by <reason>` — the induction hypothesis, the operative lemma —
    **even when a bare closer would succeed** (accepting the redundancy
    warning): we keep the explanation for the reader regardless of how
    strong the auto-prover gets.
  - Transitivity / a "`x` is strictly below itself" contradiction reads as
    an inequality **`≤`-chain**, never a positional `transitive` call — and
    it ends in `done`, not `absurd` plumbing (state `False;` first when the
    surrounding goal isn't itself the contradiction):
    ```
    1 + v ≤ m by below
          ≤ v by atLeast;
    False;
    done
    ```
  - Argument-free `by <Lemma>` works for a `≤`/`∣` chain step and any goal
    that pins the lemma's conclusion. It does **not** work for an `=` chain
    step (diff-inference needs the lemma *applied*), nor when a lemma
    premise is a *derived term* rather than a context hypothesis (the
    prover can't conjure it) — there, keep that one argument explicit,
    or pick a premise-free lemma.

- **Universe annotations (`Sum.{0,0,0}(…)`, `Product.{0,0}(…)`) are
  noise.** `Sum`/`Product` are universe-polymorphic and can't infer their
  levels at `Type(0)`. Use the `Type(0)` aliases **`DisjointUnion(A, B)`**
  (`Logic.sum`) and **`Pair(A, B)`** (`Logic.product`) for the *type*
  positions, and write the constructors **bare** — `Sum.left(value)`,
  `Sum.right(value)`, `Product.make(a, b)` — they infer their levels and
  component types from the expected type. The one spot that needs help is a
  relation chain's *head* (no expected type): give it a one-line
  ascription `(Sum.left(…) : DisjointUnion(A, B)) = …`. `cases`/patterns
  over the aliases work unchanged (they unfold to `Sum`/`Product`).

- **The hole marker is `?`, never `_`** (`_` parses as an identifier).
  `?` is solved from the expected type in direct-goal position — e.g.
  `Foo.equal_of_value(n, ?, b, valueProof)` against a goal `a = b` solves
  `? = a`. It mis-resolves inside a `congruenceOf`/chain-step `by`
  position, so spell those.

The litmus test: a reader should follow the proof as *mathematics* —
"apply `g` to both sides", "by antisymmetry", "`1 + v ≤ m ≤ v`,
contradiction" — without parsing CIC bureaucracy. Length spent on named
mathematical steps is a feature; ceremony is the enemy.

### Statement-level proof sugar

`reference.md` catalogues the statement grammar (stated facts, `take`,
`suppose`, `let`, `witness`/`choose`, `note`). What follows is the
judgment: which form reads as mathematics where.

- `<type> by <proof> as <name>;` — assert and discharge, named for later
  citation. To close the current goal (type from the surrounding expected
  type): bare `done` / `okay`, or with a hint `done by <proof>` /
  `okay by <proof>` (the auto-prover closes a bare `done`/`okay`).
- `<type> by <hint>;` — anonymous stated fact. Hints include `by
  (<fact>)` (cite a proposition: auto-proved, then used as a proof of
  itself — below), `by substitution` (auto-find equality + body), `by
  substituting <eq>` (narrowed to a supplied equation — `<eq>` may be a
  proof *or* a bare equation `(a = b)`, which is auto-proved), `by cases
  { … }`, `by cases on E { case A: … case B: … }`, `by induction { … }`.
- **Split a disjunction with `done by cases { case LEFT as x: … case RIGHT
  as y: … }`** — the arms list the disjuncts as propositions
  (no `Or.introduce*` constructor names), and the auto-prover supplies the
  covering `LEFT ∨ RIGHT` from whatever's in scope — a hypothesis, a local
  stated fact, or a re-derived lemma — so the scrutinee never has to be
  named. (The covering disjunction must be exhaustive, of course; that is
  the only requirement.)
- `<proofTerm>;` — when the argument is already a **proof** (a
  hypothesis, a cited lemma), stating it bare introduces its *type* as
  the fact, with that proof — the mirror of the proposition-as-proof
  coercion (a proof position may take a proposition; here the
  proposition position takes a proof). Lets a named fact enter context
  without restating its (often long) type: `Rational.is_commutative_ring;`
  adds the `IsCommutativeRing(…)` fact. Assembling a bundle from its named
  components reads as `a; b; c; done` — and because each
  fact is exact-typed, the `done` conjoins them directly (no expensive
  decomposition), so this is the form for `⟨a, b, c⟩`-style structure
  proofs (`IsField`, `IsEquivalenceRelation`, …), not a tuple.
- **Eliminating an existential — prefer `choose`.**
  `choose <name> [such that <prop>] [as <condName>] from <source>;` shows —
  and the kernel verifies — *what the witness satisfies* in place, and
  avoids the `⟨…⟩` tuple pattern. `from` takes a hypothesis (naming *which*
  `∃` when several are in scope), a lemma cited argument-free, or any
  applied term of existential type; omitted, the most recent in-scope `∃`
  is used. `such that` is preferred (the full existential body — a
  conjunction is fine), and doubles as the disambiguator for a lemma
  source. Omit `as` unless the condition is later cited by name.
  Example: `choose gap such that a + (1 + gap) = b from Natural.lt_elim;`.
- A context **conjunction's legs are facts on their own**: a hypothesis
  `A ∧ B` lets you prove/cite `A` or `B` directly — no manual `And.left`/
  `And.right`. So after `choose x such that A ∧ B from h;`, both `A` and `B` are
  usable in by-less / `by` / `substituting` steps.
- `let ⟨a, b⟩ := <expr>;` — the tuple destructure, reserved for genuine
  **data records** (a quotient representative, `Subtype`, a bundle) where
  naming several components flatly is what's wanted. For an `∃`/`∧`, use
  `choose` / the leg-facts above — the `⟨…⟩` is an implementation tell that
  the connective is encoded as a tuple. (`obtain` is retired.)
- **Building a connective — symmetric to destructuring it.** Don't write the
  constructor tuple either. To prove `A ∧ B`, state the parts and let the prover
  conjoin: a bare `done`, or `A by …; B by …; done`. To prove
  `∃ x. P`, `witness v with <proof of P(v)>`. To project a single axiom out of a
  bundled proof — associativity from an in-scope `IsGroup`, a leg of `IsRing`
  brought in by `IsRing(…) by <r>.is_ring;` — a bare `done` suffices;
  the prover decomposes the conjunction and finds the leg. (`⟨proofA, proofB⟩` /
  `⟨v, proof⟩` are the construction-side tells.) Genuine data records (`Ring`, a
  representative, `Subtype`) really are tuples, so `⟨…⟩` and `by_representatives x
  as ⟨a, b⟩` are correct there — the distinction is the *type*: a logical
  connective vs. a data structure.
- **Audit:** `make anon-tuple-report` (set `MATH_CHECK_ANON_TUPLES=1`) is the
  type-aware check that flags every user-written `⟨…⟩` built or destructured at
  `And`/`Exists`, while leaving data-record tuples, `witness`, and `choose`
  untouched. (Manifest-scoped; a regular `cic_leak_report` run does NOT see this
  axis.)
- `cases by <lemma> { … }` — the same inference for a **case-split**: cite
  `<lemma>` argument-free (premises from context) and case-split on the
  disjunction / inductive it yields. E.g. `cases by
  Natural.divides_less_or_equal_or_zero { … }`. (Only when the lemma's premises
  pin its data arguments — a premise-less lemma like `totality_of_less_or_equal`
  can't be cited this way.)
- **Multi-argument helper with derived premises.** To discharge a helper that
  takes several data arguments and several proof premises (some of them derived
  — e.g. `quotient_strict_absurd`), state any derived premise as a bare
  fact/relation chain so ALL its premises are in context, then state the
  `<conclusion> by <helper>`: backward chaining discharges every premise
  from context and pins all the data arguments as a side effect. Caveat:
  this search can be expensive — if the helper's premises themselves
  invite a wide search (e.g. `multiply_at_least_one` among many in-scope
  facts) it may not terminate in budget; keep those explicit.
- **Proving a disjunction `A ∨ B`.** State the true disjunct and let the
  auto-prover introduce the `∨`: `A by <reason>; done`,
  NOT the raw constructor `Or.introduceLeft(<proof of A>)`. `done`'s
  disjunction-introduction picks whichever disjunct is in context. (Same for
  proving a universal: prefer `take x; …` — introduce the variable — over a
  point-free function value; see `Natural.totality_of_less_or_equal`.)
- **Deriving a contradiction — end in `done`.** The polished idiom is to
  put the contradictory facts in context (a fact and its negation, a
  ground-false equality, a chain landing on `x < x`-shaped composites)
  and close with `done` — inside `suppose … for contradiction { … }`,
  state `False;` first when the surrounding goal is not itself the
  contradiction. `absurd(<proof-or-proposition>)` still exists as the
  explicit closer, but reads as plumbing; prefer stating the false fact
  and letting `done` refute it.
- **Introduce a goal's `∀`/`→` binders with `take`/`suppose`, not a
  restated-type lambda.** For a goal `∀ (a b : T). P(a) → P(b) → C`, open the
  proof with `by { take a; take b; suppose P(a) as ha; suppose P(b) as hb;
  … }` — NOT `by (a b : T) (ha : P(a)) (hb : P(b)) ↦ { … }`, which
  bureaucratically restates every binder's type straight from the statement.
  The intros read like "take a, b; suppose ha, hb" and never duplicate the
  signature. (Binders the prover later consumes by type — e.g. an `as`-named
  disjunction fed to a `by cases` — don't trip the unused-name check.)
- `suppose Not(G) [as h] for contradiction;` — reductio, **terminal**.
  Assume `Not(G)` (the negation of the goal), derive `False` through the
  rest of the block (e.g. ending in `contradiction;`), and the goal `G`
  is closed by double-negation elimination. Reads as "suppose, for
  contradiction, that …". The `as h` is optional — omit it when the
  assumption is consumed by the prover rather than named.
- `suppose Not(X) [as h] for contradiction { … };` — reductio,
  **forward**. The braces scope the `False`-derivation: assuming
  `Not(X)`, the block derives `False`, which establishes `X` into the
  context (anonymously, for the auto-prover to pick up by type), and the
  proof then **continues at the original goal**. Use this to prove an
  intermediate fact `X` by contradiction mid-proof; the terminal form is
  the special case where `X` is the goal and nothing follows. To name the
  established fact, state the terminal form's type and name it:
  `X by { suppose Not(X) for contradiction; … } as hx;`.
- `suppose P [as h] for proving Q { … };` — forward implication intro.
- `take x : T for proving Q { … };` — forward ∀-introduction (same grammar).
  Prove `Q` under the hypothesis `h : P` inside the block, which adds
  `P → Q` to the context (anonymously, for the auto-prover to pick up by
  type) for the rest of the proof. Reads as "suppose `P`; to prove `Q`: …".
- `note goal : <type>;` — assert the current expected type is
  definitionally equal to `<type>` and continue. Reads as
  "we need to show that …" / "the goal is …". A no-op at the term
  level — pure scaffolding that documents the goal at a point where
  the reader benefits from seeing it (right after `take`s, after a
  `cases` split, before a long chain). The elaborator runs
  `isDefinitionallyEqual` and reports a mismatch with both forms in
  the error.
- `note <proposition> [by <proof>];` — a *verified comment*: like a
  bare stated proposition, except it does **not** add the fact to the
  context. Reads as "note
  that …" / "observe that …" — a parenthetical aside in math prose. With
  no `by`, the auto-prover must close `<proposition>`; with `by <proof>`
  the reason is shown (and the note holds even when the auto-prover
  couldn't close it alone). Because it adds nothing to the context and is
  for the reader, it is never flagged unused or redundant. Use it to keep
  an intermediate fact visible even when the surrounding proof would close
  without it.
- `change <type>;` — the *active* counterpart of `note goal`: assert
  `<type>` is definitionally equal to the current goal AND replace the
  goal by `<type>` for the rest of the block (the body is elaborated at
  `<type>`). The one-line escape hatch for a residual defeq-spelling
  mismatch — write the spelling your next step needs, instead of the
  ad-hoc `<type> by <oldGoalProof> as X;` bridge. (`note goal : T`
  only *checks*; `change T` checks and *switches*.)
- `unfold <Foo> in <body>` — temporarily mark `Foo` transparent
  inside `<body>` (for opaque definitions; see `conventions/opaque.md`).

### When to hint: prefer the auto-prover, explain only reasons

The guiding light is what a mathematician would write. Most of the
time that means **leaning on the auto-prover and citing nothing** —
a by-less chain step or a bare `P;` reads like "clearly" /
"and so", which is exactly how a proof flows when the step is routine.
Spell a justification out only when a *human or LLM reader* genuinely
benefits from it.

When you do justify a step, point at the **reason it is true**, not the
**mechanism that discharges it**. The name of a mundane plumbing lemma
(`add_general_LessOrEqual_left`, `halve_preserves_LessOrEqual`) is
mechanism — the reader learns nothing from it, so prefer a by-less step
with a short prose reason in a comment, or none at all. Reserve a cited
hint for when the *named result itself* is the insight.

So, in order of preference for a step the auto-prover can close:

1. **Nothing** — by-less chain step / bare `P;`. The default.
2. **`note P [by …];`** — surface an intermediate fact for the reader
   without binding it into context (the proof closes without it). The
   "observe that …" aside.
3. **`P by <Lemma>;`** / `… = b by <Lemma>` *kept despite the
   redundancy warning* — for the rare step where the named result
   itself is the insight (the induction hypothesis, a closed form, a
   big-name theorem). The redundant-`by` check will flag it; keeping
   it anyway is the author's judgment call, and that judgment — not a
   keyword — is what marks the hint as reader-load-bearing.

When the prover **cannot** close the step without help, the citation
isn't an explanation — it's load-bearing. Prefer, in order:

1. **`by (<fact>)`** — cite the *proposition* that does the work, in
   parentheses. It is auto-proved and then bridged to the goal exactly
   like `by <proof-of-that-fact>` (congruence/unification — see
   `conventions/structures-and-inference.md`). Prefer this over a lemma name **when
   the fact is simple**: `by (a = b)` or `by (x ≤ y)` tells the reader
   *what's true*, not which plumbing lemma fires. (Judgement call — a
   short, meaningful fact; not a restatement of the whole goal.)
2. **`by <lemma>`** — name the lemma, arguments inferred. Use when the
   *named result itself* is the insight, or when no single fact bridges
   the step (a combining lemma is needed — then `by <lemma> recalling
   (<fact>)` supplies its premise; see `conventions/structures-and-inference.md`).
3. **`by <lemma>(args)` / `by <proof>`** — spell it out only when
   inference can't fill the arguments.

`by (<fact>)` bridges a fact whose proof *directly* establishes the goal
(equalities via congruence, conclusion-matching facts); it does **not**
chain through a combining lemma or flip by symmetry — for those, name the
lemma (optionally `recalling (<fact>)`). Example where the `by` is
genuinely load-bearing: `(0 : Rational) ≤ (n : Rational) by
Rational.LessOrEqual_zero_of_IsNonneg((n : Rational), Rational.from_-
natural_is_nonneg(n))` — the prover can't reach `IsNonneg(n)` on its own.

Outermost-arm shorthands for case-splits:

- `by induction on n with IH { case n = 0: … case n = 1 + k for some k: … }` —
  preferred over a pattern-match definition.
- Hypotheses about `n` refine automatically per arm (and the IH
  quantifies over them); `by induction on n with IH generalizing b { … }`
  loads the IH over extra binders.
- `by induction on n using <strongRecursionLemma> { … }` — route
  the recursion through a user-supplied recursion principle.
- `by strong induction on n with IH { … }` — strong induction on a
  Natural; IH has type `(k : Natural) → k < n → P(k)`.

`done` and `okay` are both a bare restatement of the `goal` — pick
whichever spells the proof's intent: "the proof is done here" (`done`),
"okay, that proves it" (`okay`). (`goal` on its own is just the name of
the goal type, not a closer.)

The remaining subsections are about *CIC noise* — bureaucracy that
the kernel demands but a mathematician would never write. Those
should be hidden behind named helpers; the rules below collect the
ones that come up most often. None of these rules trade away
readability — they only remove ceremony.

### `<order>.weaken` over `And.left` on a `<` hypothesis

`Rational.LessThan(x, y)` unfolds to `And(LessOrEqual(x, y),
Not(x = y))`. With `x < y` in scope and a goal needing `x ≤ y`, state
the fact and cite the named face:

```math
x ≤ y by Rational.LessThan.weaken;
```

never the tuple projection

```math
And.left(Rational.LessOrEqual(x, y), Not(x = y), h)
```

Same for `¬(x = y) by Rational.LessThan.distinct;` vs `And.right(…)`. Helpers live in `Rational/order_arithmetic.math`
alongside `LessOrEqual.negate`, `LessThan.negate`,
`negate_LessThan_zero_of_positive`, `LessOrEqual_zero_of_negate_IsNonneg`.

## `--goal-at` — ask what the goal is at a line

A poor man's infoview: when you are mid-proof and unsure what remains to
be proven (or what hypotheses are in scope), put a `sorry` where you are
stuck and query its line:

```
./kernel verify --source <file>.math --cache-root build --goal-at <line>
```

It prints the hypotheses and goal at the proof statement at (or nearest
before) that line — pointing anywhere inside a multi-line statement
reports the enclosing statement (hypotheses, then `⊢ <goal>`).

The report is printed even when elaboration fails *after* the queried
line, so a half-written proof still answers "what was I proving here".
`--output` is optional for a query-only run (no cache is written without
it).

## Polishing with the redundancy checks (and the cascade they trigger)

The kernel has three opt-in diagnostics for trimming dead hints (they are
NOT part of the normal `make`, which stays clean either way — these are a
deliberate polishing pass, somewhat expensive, run on *your* files only):

```
./kernel verify --source <file> --output <…>.mathv --cache-root build --check-redundant-by
                                                                       --check-redundant-by-non-eq
                                                                       --check-redundant-calc-steps
```

`--check-redundant-by` reports both a *redundant-`by`* finding (the
auto-prover closes the step/stated fact without the hint) and an
*unused-name* finding (a binding the prover consumes by type-match, so
the name is dead weight). `.mark_redundant.py <files>` annotates the
chain-step `by` sites with marker
comments; you then **edit by hand and rebuild**, reverting anything that
turns out to be load-bearing (the checker tests each site in isolation, so
adjacent steps in a chain can interact). Do NOT write a fully-automated
rewriter.

**How to resolve each finding — by readability, not by chasing zero:**

- **Redundant `by` on a *chain step* citing a library lemma / tactic**
  (`by ring`, `by multiply_commutative`) → make it
  **by-less**. The chain already shows the intermediate form; the
  citation was noise.
- **Redundant `by` on a *stated fact* that names the operative lemma**
  (often with a long positional argument list) → go **argument-free**
  (`by <Lemma>`) and then decide: if the named result is genuinely the
  insight (IH, a closed form, a big-name theorem), **keep it** and
  accept the persistent warning; otherwise **bare the fact** — the
  stated proposition is its own explanation.

**The cascade — expect it, and settle it.** Removing a `by` (or going
argument-free) makes the auto-prover pick the needed fact out of context by
*type-match* instead of by name. Two follow-on findings appear:

1. A named intermediate `T by … as NAME` whose `NAME` is now only
   consumed by type-match → flagged **`unused name`**. Fix: **anonymize**
   it — `T by V;` (or bare `T;` if its own `by` was also
   redundant). The fact is still stated and still in context for the
   type-match; only the dead label goes. Keep a name **only** when it is
   referenced by name later (a genuine milestone).
2. A chain step that fed such a stated fact may itself become redundant
   → by-less it too.

Re-run the check after editing; the cascade is finite and converges to
by-less routine steps + anonymous intermediate facts + a few kept
`by`-cited operative lemmas (flagged, deliberately). Stop short of churning when removal would *worsen*
things: by-less'ing a step that cites a `choose`/`suppose` binder just
moves the warning to an "unused binder" (use `as _`, or leave it); and a
genuinely informative reduction *chain* is worth keeping even when the
prover could skip it.

**`by` vs `note` — the mnemonic.** `by` = the prover needs it (or the
author insists the reader does — a kept, flagged hint). `note P [by …];`
= a verified comment that is **not added to the context** — so never use
`note` for a fact a later step must consume by type-match (it won't be
there); state it bare (anonymously) for that.

## Check the result

Build the library:

```sh
make -j 16 library
```

For language and elaborator work:

```sh
make -j 16 tests
```

For files in the clean manifest:

```sh
make clean-check
make clean-anon-ratchet
```

The redundancy checks can find removable hints and unused names, but their
output is a polishing aid rather than a substitute for reading the proof.
The final test is whether the proof communicates the mathematical argument.

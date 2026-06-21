# Proof style and statement-level sugar

Write proofs that read like math: `cases`/`by_induction` over pattern-match, `cases … with`, `decide`, the statement-level sugar (`claim`/`obtain`/`take`/…), and CIC-noise-reduction idioms.

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

## Prefer `cases` / `by_induction` over pattern-match definitions

The pattern-match definition form (`theorem foo | zero => … |
successor(k) => …`) is supported but NOT the preferred style.
Mathematicians don't write proofs as separated equation cases at the
outer-syntax level — they write a body that opens with "by cases"
or "by induction on n" and then handles each constructor.

Translation:

```math
-- Pattern-match (legacy):
theorem Natural.foo : (n : Natural) → P(n)
  | zero          => baseProof
  | successor(k)  => stepProof(k)

-- Preferred — non-recursive case split:
theorem Natural.foo (n : Natural) : P(n) :=
  cases n {
    | zero          => baseProof
    | successor(k)  => stepProof(k)
  }

-- Preferred — recursive (k's IH needed in stepProof):
theorem Natural.foo (n : Natural) : P(n) :=
  by_induction on n with IH {
    case zero:           baseProof
    case successor(k):   stepProof(k, IH)  -- IH : P(k)
  }
```

Pattern-match definitions remain unavoidable for direct recursion
that doesn't fit `by_induction`'s motive shape — for example when
the conclusion is universally quantified over a parameter that the
IH must be polymorphic over (`Natural.decides_equality` recursing on
`a` while the IH must work for all `b`). Use the `cases` body style
by default; reach for pattern-match definitions only when the
recursion really demands it.

### Multi-pattern bindings (when the pattern-match form is used)

Constructor patterns at non-scrutinee positions of a pattern-match
definition properly refine the types of later-bound args
(including dependent equality hypotheses). Write all destructures in
one row:

```math
theorem IntegerEquivalent.symmetric
        : (x y : IntegerRepresentative)
          → IntegerEquivalent(x, y)
          → IntegerEquivalent(y, x)
  | IntegerRepresentative.make(a, b),
    IntegerRepresentative.make(c, d),
    aPlusDEqualsBPlusC ↦
      …
```

The elaborator emits a nested recursor chain whose motives abstract
the destructured position AND every later position binder, so a
hypothesis like `aPlusDEqualsBPlusC` arrives in its refined
Natural-level form. Inner constructor patterns are supported on
single-constructor non-indexed non-recursive (parameterised OK)
inductives — covers `IntegerRepresentative.make`,
`RationalRepresentative.make`, `PAdicCauchySequence.make`. Multi-
constructor inner positions would need per-row coverage analysis
that isn't yet wired up.

## `cases ... with` — case-split with retained equation

To case-split on an expression and retain an equation between the
expression and the matched form, add `with <equalityHypothesisName>`:

```math
cases Integer.absolute_value_natural(x) with refinedEquation {
  | zero          => ...refinedEquation : Integer.absolute_value_natural(x) = zero...
  | successor(k)  => ...refinedEquation : Integer.absolute_value_natural(x) = successor(k)...
}
```

The elaborator desugars this to the convoy pattern (`(caseScrutinee : T) (equalityOuter : X = caseScrutinee) ↦ …`) — the user just picks a name. Each arm gets `refinedEquation` in scope with the type refined per branch.

Constructor patterns with arguments (e.g. `successor(predecessor)`) are reconstructed as expressions for the equation type; tuple patterns aren't yet supported.

## `decide P { yes m => … | no n => … }` — classical case-split

The canonical form for classical case-splits. Replaces both:

- `cases Logic.excluded_middle(P) { | Or.introduceLeft(m) => … | Or.introduceRight(n) => … }` (for plain "P or not P" reasoning at the proposition level), AND
- `cases Logic.classical_decidable(P) with decisionEq { | Decidable.yes(m) => transport(…, m) | Decidable.no(n) => transport(…, n) }` (for the bisection-style pattern where the goal contains `bisectionStepWithDec(…, classical_decidable(P))` and we want each arm checked at the ι-reduced shape).

```math
-- Simple proposition-level case split (no goal abstraction needed):
decide x = Real.zero {
  | yes xEqZero  => Or.introduceLeft(IsNonneg(x), IsNonneg(-x), rewrite(…))
  | no  xNotZero => /* recurse with the inequality */
}

-- Bisection-style: the goal `Real.IsUpperBound(subset, right(bisectionStep(…)))`
-- has `classical_decidable(IsUpperBound(subset, midpoint))` buried five δ
-- unfoldings deep. The elaborator finds it (head-directed WHNF walker)
-- and abstracts the motive automatically — each arm proves its
-- ι-reduced shape.
decide Real.IsUpperBound(subset, (midpoint : Real)) {
  | yes midIsUpper => midIsUpper      -- new_right = midpoint
  | no  _          => IH              -- new_right = right(predecessor)
}
```

Semantics: builds `Logic.Decidable_recursor(P, motive, λp. arm_yes, λn. arm_no, Logic.classical_decidable(P))`. The motive abstracts every structural occurrence of `Logic.classical_decidable(P)` in the goal (after δ unfolds chained definitions like `bisectionStep`); if none appears, motive defaults to `λ_. Goal` and each arm proves the goal directly with `p` / `notP` in scope.

What it eliminates:
- The motive-as-lambda boilerplate (`(decision : Logic.Decidable(…)) ↦ …`).
- The explicit `Equality.transport_proposition(…)` call wrapping each arm.
- The `with decisionEq` equation plumbing.
- The `Or.introduceLeft` / `Or.introduceRight` constructor names.

When `decide` doesn't apply: the goal mentions some OTHER decidable expression (not the user's `P`), so the head-directed search finds no `classical_decidable(P)` and the motive falls back to constant. That's fine — it's the same as the old `cases Logic.excluded_middle(P)` pattern, just spelled more clearly. Either binder name may be `_`.

Two things that work and used to require `_step` helper splits (see
Lists/filter.math for the natural style):

- **Recursion in arms.** In a pattern-match definition or theorem, a
  self-call inside a `decide` arm resolves to the induction hypothesis
  like anywhere else in the case body.
- **Occurrences under a Pi.** The motive abstraction sees
  `classical_decidable(P)` on the hypothesis side of an implication
  goal too (it unfolds Pi domains with the same gated WHNF walk as the
  conclusion). So a lemma `member(filter(P, prepend(h, t))) → …` can
  open directly with `decide P(h)`, and each arm `suppose`s the
  membership at its ι-reduced form (`prepend`-form in `yes`, tail-form
  in `no`).

Error diagnostic: if the assembled `Decidable_recursor` application doesn't typecheck, the elaborator pre-checks it and dumps each of the 5 arg slots (proposition / motive / yes case / no case / scrutinee) with its inferred type, so the error points at which slot is the culprit. Generic kernel "Application: argument type does not match Pi domain" errors anywhere in the file now also print `expected type:` and `actual type:` lines.

## Introducing a disjunction — state the side, skip `Or.introduce*`

To prove an `A ∨ B` goal you don't have to name `Or.introduceLeft` /
`Or.introduceRight`. Two by-less options, in preference order:

- **`claim`** — let the auto-prover prove the whole disjunction: it tries
  `A`, then `B`, from context and wraps the matching constructor. Best when
  the winning side is *cheap* for the prover (a hypothesis, reflexivity, a
  short transitivity chain). It will also close sides that need a library
  search, but that can be slow — don't lean on it for a disjunct that needs
  a specific cited lemma plus algebra.
- **State the side directly** — give a proof whose type *is* one disjunct
  (a hypothesis, a `calc`, a lemma application) and the **disjunction-
  injection coercion** wraps the right constructor. This is a targeted,
  search-free coercion (it matches the proof's type against each disjunct up
  to definitional equality), so it's the right tool when the side needs real
  work the prover wouldn't find:
  ```math
  cases quotient refining nEqualsDtimesQuotient {
    -- n = d·0 = 0 — the left disjunct.
    | zero => calc n = d * 0 = 0
    -- n = d·(q′+1) = d + d·q′ ≥ d — the right disjunct.
    | successor(quotientPredecessor) =>
        calc d ≤ d + d * quotientPredecessor
                  by Natural.less_or_equal_add_right(d, d * quotientPredecessor)
              = d * successor(quotientPredecessor)
              = n
  }
  ```
  Both arms read as the mathematics ("n is 0", "n ≥ d") with the `Or` wrapper
  inferred. Spell out `Or.introduceLeft` / `Or.introduceRight` only when the
  proof term is itself ambiguous about which side it proves.

## Proof style — write proofs that read like math

The overriding goal is that a proof reads like what a mathematician
would write in a textbook, with the kernel doing the typechecking. A
human should be able to scan the proof and follow the argument
without parsing CIC bureaucracy. The optimization target is
**readability**, not terseness.

Concretely:

- **No abbreviations.** Both in identifiers (see the Naming section
  above — `representative`, not `rep`, in declared names) and in
  binders within proofs. Verbosity that aids comprehension is a
  feature, not a cost — `halvedEpsilonPositive`, not `hep`.

- **Math-like phrasing.** Compose the proof out of named
  mathematical steps. A reader should see "triangle inequality on
  (a − b) and b", "subtract |b| from both sides", "case split on
  the sign of (|a| − |b|)" — not a wall of `congruenceOf` /
  `transport_proposition` calls.

- **Length is fine if it's pedagogical.** Don't golf. A 40-line
  proof that explains each step in *named mathematical steps* is better
  than a 10-line proof that requires unwinding three nested
  `Quotient.lift` calls in your head to follow. But the explanation
  belongs in the proof code — a `calc` chain, named `claim`s, `since`
  citations — not in a comment narrating what the code should already say
  (see the comment maxim below).

- **`calc` is encouraged.** It mirrors how a mathematician writes
  an equation chain. Use it whenever you can name each intermediate
  form. Even a two-step calc is usually clearer than the equivalent
  `Equality.transitivity(...)`.

- **A comment is an admission of defeat — make the *proof* carry the
  reasoning.** The aspiration (borrowed from good C++ practice) is that the
  proof reads like the mathematics on its own; a comment is a signal that a
  step wasn't saying enough. Triage every comment:
  - **A "what" comment is defeat.** `-- b divides 0 (every n divides 0)` over a
    bare `claim b ∣ 0;` puts the *reason* in prose, not code. Push it into the
    proof — `claim b ∣ 0 since Natural.divides_zero;` — and delete the comment.
    The lever is almost always a `since <named-lemma>`, a named `claim`, a
    `calc` form, or `take`/`suppose`. (A claim stays bare only when a
    *tactic/computation* closes it — `ring`, defeq, the equality battery —
    where there is no lemma to name; see "don't justify routine computation".)
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

- **Sequence-of-claims style is encouraged.** When a proof has
  several distinct subgoals, write them as a sequence of `claim
  <name> : <type> by <proof>` lines and then assemble the result
  from the named claims. This makes the structure of the argument
  legible and lets a reader skim the claims to see the shape before
  reading the inner proofs.

### What an ideal proof looks like — and the CIC tells that betray it

Write the proof a mathematician would, then make the kernel accept it —
NOT the other way around. The single biggest readability failure is
**raw-CIC style**: the proof typechecks but reads like type theory, not
mathematics. If you find yourself writing any of the following, stop and
reach for the math-like form instead:

- **`congruenceOf(…)` / `Equality.congruence(…)` — a raw-CIC stink.**
  "Apply `f` to both sides of `a = b`" is a one-step `calc` whose
  justification is the inner equality: the elaborator's *diff-inferred
  congruence* wraps `f` automatically (see calc-and-rewrite.md).
  ```
  -- NOT: congruenceOf((x) ↦ Sum.left(A, B, x), valueEquality)
  calc Sum.left(A, B, recovered)
     = Sum.left(A, B, original)   by valueEquality        -- congruence inferred
  ```
  Caveat: after a `cases`/`refining` has already reduced the goal, the
  function application in the goal is *already* the reduced constructor
  form, while a freshly-written `f(g(x))` is *stuck* (neutral scrutinee).
  So **start the calc from the reduced form**, not from the original
  application.

- **`Equality.symmetry(…)` to flip an equation is usually unnecessary.**
  A `calc` `=` step's diff-inference already tries both orientations, so a
  *reversed* step needs only `by <lemma/hypothesis>` — `by bEquation`, not
  `by Equality.symmetry(bEquation)` — and the binder stays referenced. When
  the reversed equation is needed in *argument* position (no calc step to
  flip — e.g. feeding `equal_of_value` or another lemma), wrap it in a
  one-step `calc B = A by <proofOfAeqB>` rather than calling
  `Equality.symmetry`.

- **`claim NAME : a = c by calc a = … = c` is ceremony** — the calc's
  endpoints already *are* `a = c`, so the `claim NAME : <type> by` wrapper
  just restates it. Bind the calc's result directly:
  ```
  -- NOT: claim quotientLeK : n * q ≤ k by calc n * q ≤ n * q + r = k;
  calc n * q ≤ n * q + r = k   as quotientLeK;
  ```
  Use `calc … as NAME;` when the result is referenced later by name, and a
  bare `calc …;` when it's only consumed by type-match (see calc-and-
  rewrite.md, "`calc … as NAME;` and bare `calc …;` at statement position").
  And when the calc *is* the whole proof, it is the proof — write `:= calc
  …` / return the `calc`, never `claim <goal> by calc …`.

- **`Equality.transport_proposition(…)` to move a fact along an
  equation** — use a `calc` step or `by substituting <eq>` instead.

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

- **Direct proof-lemma calls** — applying a `theorem` to positional
  arguments — are discouraged *entirely*, at every arity. Not just
  `LessOrEqual.transitive(a, b, c, p, q)` but also the one-argument
  `successor_less_or_equal_successor(proof)`: both invoke the lemma as a
  function instead of reading as mathematics. **State the fact and
  discharge it by name, argument-free**: `claim T by <Lemma>` (which binds
  `T` into context), or chain it via `calc`,
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
    `by_induction on a with IH refining b, c, h { case zero: … case
    successor(predecessor): … }` instead: the hypothesis is the named local
    `IH`, cited argument-free like any fact (`done since IH` / `done by IH`),
    so the recursion both reads as induction and is no longer a lemma call.
    Example — `Natural.add_cancel_left` (`library/Natural/arithmetic.math`):
    ```
    by_induction on a with IH refining b, c, equalityHypothesis {
      case zero: equalityHypothesis
      case successor(predecessor): {
        claim predecessor + b = predecessor + c;   -- strip the successor
        done since IH
      }
    }
    ```
    This also works for induction on a **derivation** (an indexed inductive
    `Prop`, e.g. a `≤` proof). Use the constructor names as cases, and
    `refining <h>` for a hypothesis whose type mentions an index that the
    induction varies. Example — `LessOrEqual.transitive`:
    ```
    by_induction on bc with IH refining ab {
      case LessOrEqual.reflexivity(_): ab                       -- b = c
      case LessOrEqual.step(_, cPredecessor, _):
          LessOrEqual.step(a, cPredecessor, IH(ab))             -- one more step
    }
    ```
    The case bodies use the constructor's *destructured* index names, not the
    outer binders; `IH` (or `IH(<refined-hyp>)`) is the named hypothesis.
  - **Closers.** `done` and `okay` are precisely `claim goal` — a claim
    whose proposition is the `goal` (the expected type). A bare `done`/`okay`
    discharges the goal by lookup; each also takes an optional `by <hint>`
    (prover needs it) or `since <reason>` (kept explanation). `goal` itself is
    only the NAME of the type being proved — a type reference (`claim goal`,
    `note goal : T`), NOT a standalone closer (`goal by …` is rejected; write
    `done by …` / `okay by …` / `claim goal by …`). Prefer **`since`** for an
    illuminating reason — the induction hypothesis, the operative lemma —
    **even when a bare closer would succeed**: we keep the explanation for the
    reader regardless of how strong the auto-prover gets.
  - Transitivity / a "`x` is strictly below itself" contradiction reads as
    an inequality **`≤`-calc**, never a positional `transitive` call:
    ```
    claim valueBelowItself : successor(v) ≤ v
        by calc successor(v) ≤ m by below ≤ v by atLeast;
    absurd(Natural.not_successor_less_or_equal_self(v, valueBelowItself))
    ```
  - Argument-free `by <Lemma>` works for a `≤`/`∣` calc step and any goal
    that pins the lemma's conclusion. It does **not** work for an `=` calc
    step (diff-inference needs the lemma *applied*: `by add_successor(m,
    x)`), nor when a lemma premise is a *derived term* rather than a
    context hypothesis (the prover can't conjure it) — there, keep that one
    argument explicit, or pick a premise-free lemma (`successor_positive`
    over `successor_less_or_equal_successor`).

- **Universe annotations (`Sum.{0,0,0}(…)`, `Product.{0,0}(…)`) are
  noise.** `Sum`/`Product` are universe-polymorphic and can't infer their
  levels at `Type(0)`. Use the `Type(0)` aliases **`DisjointUnion(A, B)`**
  (`Logic.sum`) and **`Pair(A, B)`** (`Logic.product`) for the *type*
  positions, and write the constructors **bare** — `Sum.left(value)`,
  `Sum.right(value)`, `Product.make(a, b)` — they infer their levels and
  component types from the expected type. The one spot that needs help is a
  `calc` *head* (no expected type): give it a one-line ascription
  `calc (Sum.left(…) : DisjointUnion(A, B)) = …`. `cases`/patterns over the
  aliases work unchanged (they unfold to `Sum`/`Product`).

- **The hole marker is `?`, never `_`** (`_` parses as an identifier).
  `?` is solved from the expected type in direct-goal position — e.g.
  `Foo.equal_of_value(n, ?, b, valueProof)` against a goal `a = b` solves
  `? = a`. It mis-resolves inside a `congruenceOf`/calc-`by` position, so
  spell those.

The litmus test: a reader should follow the proof as *mathematics* —
"apply `g` to both sides", "by antisymmetry", "`successor(v) ≤ m ≤ v`,
absurd" — without parsing CIC bureaucracy. Length spent on named
mathematical steps is a feature; ceremony is the enemy.

### Statement-level proof sugar

Inside a `{ … }` proof block, the following statement forms compose
naturally and read as math prose. All end with `;` and the block
returns its final non-`;`-terminated expression.

- `claim <name> : <type> by <proof>;` — assert and discharge.
  To close the current goal (type from the surrounding expected type):
  `claim goal [by <proof>]`, or its synonyms `done` / `okay`
  (`done by <proof>` ≡ `claim goal by <proof>`; bare `done`/`okay` let the
  auto-prover close it).
- `claim <type> by <hint>;` — anonymous claim. Hints include `by
  (<fact>)` (cite a proposition: auto-proved, then used as a proof of
  itself — below), `by substitution` (auto-find equality + body), `by
  substituting <eq>` (narrowed to a supplied equation — `<eq>` may be a
  proof *or* a bare equation `(a = b)`, which is auto-proved), `by cases
  { … }`, `by cases on E { case A: … case B: … }`, `by induction { … }`.
- `claim <proofTerm>;` — when the argument is already a **proof** (a
  hypothesis, a cited lemma), `claim` introduces its *type* as the fact,
  with that proof — the mirror of the proposition-as-proof coercion (a
  proof position may take a proposition; here the proposition position
  takes a proof). Lets a named fact enter context without restating its
  (often long) type: `claim Rational.is_commutative_ring;` adds the
  `IsCommutativeRing(…)` fact. Assembling a bundle from its named
  components reads as `claim a; claim b; claim c; done` — and because each
  fact is exact-typed, the `done` conjoins them directly (no expensive
  decomposition), so this is the form for `⟨a, b, c⟩`-style structure
  proofs (`IsField`, `IsEquivalenceRelation`, …), not a tuple.
- **Eliminating an existential — prefer `choose`.**
  `choose <name> [such that <prop>] [as <condName>] from <source>;` is the
  readable way to take a witness out of an `∃ x. P(x)`. It shows — and the
  kernel verifies — *what the witness satisfies* in place, and it avoids the
  `⟨…⟩` tuple pattern, which leaks that `∃`/`∧` are encoded as tuples
  (something a mathematician never thinks about). The clauses:
  - **`from <source>`** — where the existential comes from. A **hypothesis**
    name destructures that specific one (so you say *which* when several `∃`
    are in scope — what plain `choose` can't). A **lemma** name is cited
    argument-free (premises discharged from context, like `obtain … by`), then
    destructured. `from` also takes any applied term of existential type
    (`gSurjective(z)`, `Permutation.extract(a, b, sub)`, an explicit recursive
    self-call). With **no `from`**, `choose` takes the most-recent in-scope `∃`.
  - **`such that <prop>`** — optional but PREFERRED: a formally-verified,
    locally-readable assertion of the witness's property, so the reader needn't
    hunt in the lemma's statement or unfold a definition (`∣`, `Equinumerous`).
    Give the full existential body — a conjunction is fine (`such that A ∧ B`).
    For a *lemma* source it is also the disambiguator when several context
    facts could discharge the premise.
  - **`as <condName>`** — names the chosen condition for later citation; omit
    it and the condition joins the context anonymously, to be consumed by
    type-match in a by-less / `by` / `substituting` step (the usual case).
  Example: `choose firstQuotient such that b = a * firstQuotient from aDividesB;`
  or, citing a lemma, `choose gap such that a + (1 + gap) = b from Natural.lt_elim;`.
- A context **conjunction's legs are facts on their own**: a hypothesis
  `A ∧ B` lets you prove/cite `A` or `B` directly — no manual `And.left`/
  `And.right`. So after `choose x such that A ∧ B from h;`, both `A` and `B` are
  usable in by-less / `by` / `substituting` steps.
- `obtain ⟨a, b⟩ from <expr>;` / `let ⟨a, b⟩ := <expr>;` — the tuple
  destructure, now reserved for genuine **data records** (a quotient
  representative, `Subtype`, a bundle) where naming several components flatly is
  what's wanted. For an `∃`/`∧`, use `choose` / the leg-facts above — the `⟨…⟩`
  is an implementation tell that the connective is encoded as a tuple.
- **Building a connective — symmetric to destructuring it.** Don't write the
  constructor tuple either. To prove `A ∧ B`, state the parts and let the prover
  conjoin: a bare `done`, or `claim A since …; claim B since …; done`. To prove
  `∃ x. P`, `witness v with <proof of P(v)>`. To project a single axiom out of a
  bundled proof — associativity from an in-scope `IsGroup`, a leg of `IsRing`
  brought in by `claim IsRing(…) since <r>.is_ring;` — a bare `done` suffices;
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
  `calc`/`claim` so ALL its premises are in context, then `claim <conclusion>
  by <helper>`: backward chaining discharges every premise from context and
  pins all the data arguments as a side effect. Caveat: this search can be
  expensive — if the helper's premises themselves invite a wide search (e.g.
  `multiply_at_least_one` among many in-scope facts) it may not terminate in
  budget; keep those explicit.
- **Proving a disjunction `A ∨ B`.** State the true disjunct and let the
  auto-prover introduce the `∨`: `claim A since <reason>; done` (or `by`),
  NOT the raw constructor `Or.introduceLeft(<proof of A>)`. `done`'s
  disjunction-introduction picks whichever disjunct is in context. (Same for
  proving a universal: prefer `take x; …` — introduce the variable — over a
  point-free function value; see `Natural.totality_of_less_or_equal`.)
- **Deriving a contradiction — `absurd`.** `absurd(<proof>)` closes any goal
  from a proof of `False` or of a recognised contradiction (`0 = succ k`,
  `succ k = 0`, `succ k ≤ 0`). It also accepts a **proposition**:
  `absurd(0 = successor(k))` proves that proposition from context (e.g. a
  conjunction leg) and contradicts it — state the false fact directly rather
  than naming a tuple component or citing the negation lemma by hand.
- `let <name> ∈ <type> [with <predicate>];` — introduce a typed
  variable that can later be refined.
- `let <name> [: <type>] := <value>;` — ζ-tracked abbreviation
  (kernel sees through it; see the `let` section above).
- `suppose <proposition> as <name>;` — introduce a hypothesis as a
  step (useful for breaking implication arrows into named pieces).
- `take <name> : <type>;` — introduce a Pi-binder of the given type
  from the expected type. Reads as the math-prose "take an arbitrary
  <name> of type <type>" / "let <name> ∈ <type> be given". Use
  `take` over `(name : type) ↦` whenever the binder is
  the textbook "fix a variable" move; reserve `` for genuine
  lambdas that aren't intros. Semantically identical to a single-
  binder `suppose … as …` (both wrap the rest of the block in a
  lambda) but reads as the universal/Pi side rather than the
  hypothesis-naming side.
- `note goal : <type>;` — assert the current expected type is
  definitionally equal to `<type>` and continue. Reads as
  "we need to show that …" / "the goal is …". A no-op at the term
  level — pure scaffolding that documents the goal at a point where
  the reader benefits from seeing it (right after `take`s, after a
  `cases` split, before a long calc). The elaborator runs
  `isDefinitionallyEqual` and reports a mismatch with both forms in
  the error.
- `note <proposition> [by <proof>];` — a *verified comment*: like `claim`,
  except it does **not** add the fact to the context. Reads as "note
  that …" / "observe that …" — a parenthetical aside in math prose. With
  no `by`, the auto-prover must close `<proposition>`; with `by <proof>`
  the reason is shown (and the note holds even when the auto-prover
  couldn't close it alone). Because it adds nothing to the context and is
  for the reader, it is never flagged unused or redundant. Use it to keep
  an intermediate fact visible even when the surrounding proof would close
  without it.
- `since <proof>` — exactly `by <proof>` (same elaboration and
  type-checking), except `--check-redundant-by` never flags it. Use it on
  a calc step (`… = b since <reason>`) or a claim (`claim P since <reason>`)
  to keep a load-bearing hint the auto-prover doesn't strictly need but
  that explains the step to the reader. Mnemonic: `by` = the prover uses
  it, `since` = the author explains it. (`note` is the *non-binding*
  counterpart — a comment; `claim … since` keeps the fact in context.)
- `change <type>;` — the *active* counterpart of `note goal`: assert
  `<type>` is definitionally equal to the current goal AND replace the
  goal by `<type>` for the rest of the block (the body is elaborated at
  `<type>`). The one-line escape hatch for a residual defeq-spelling
  mismatch — write the spelling your next step needs, instead of the
  ad-hoc `claim X : <type> by <oldGoalProof>` bridge. (`note goal : T`
  only *checks*; `change T` checks and *switches*.)
- `unfold <Foo> in <body>` — temporarily mark `Foo` transparent
  inside `<body>` (for opaque definitions; see the opaque section).

### When to hint: prefer the auto-prover, explain only reasons

The guiding light is what a mathematician would write. Most of the
time that means **leaning on the auto-prover and citing nothing** —
a by-less `calc` step or a bare `claim P;` reads like "clearly" /
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

1. **Nothing** — by-less `calc` step / `claim P;`. The default.
2. **`note P [by …];`** — surface an intermediate fact for the reader
   without binding it into context (the proof closes without it). The
   "observe that …" aside.
3. **`claim P since <proof>;`** / `… = b since <proof>` — keep a
   load-bearing-looking citation the prover doesn't strictly need but
   that explains the step. `since` (not `by`) signals "the author is
   explaining," and the redundant-`by` check leaves it alone.

When the prover **cannot** close the step without help, the citation
isn't an explanation — it's load-bearing. Prefer, in order:

1. **`by (<fact>)`** — cite the *proposition* that does the work, in
   parentheses. It is auto-proved and then bridged to the goal exactly
   like `by <proof-of-that-fact>` (congruence/unification — see
   `structures-and-inference.md`). Prefer this over a lemma name **when
   the fact is simple**: `by (a = b)` or `by (x ≤ y)` tells the reader
   *what's true*, not which plumbing lemma fires. (Judgement call — a
   short, meaningful fact; not a restatement of the whole goal.)
2. **`by <lemma>`** — name the lemma, arguments inferred. Use when the
   *named result itself* is the insight, or when no single fact bridges
   the step (a combining lemma is needed — then `by <lemma> recalling
   (<fact>)` supplies its premise; see `structures-and-inference.md`).
3. **`by <lemma>(args)` / `by <proof>`** — spell it out only when
   inference can't fill the arguments.

`by (<fact>)` bridges a fact whose proof *directly* establishes the goal
(equalities via congruence, conclusion-matching facts); it does **not**
chain through a combining lemma or flip by symmetry — for those, name the
lemma (optionally `recalling (<fact>)`). Example where the `by` is
genuinely load-bearing: `claim (0 : Rational) ≤ (n : Rational) by
Rational.LessOrEqual_zero_of_IsNonneg((n : Rational), Rational.from_-
natural_is_nonneg(n))` — the prover can't reach `IsNonneg(n)` on its own.

Outermost-arm shorthands for case-splits:

- `by_induction on n with IH { case zero: … case successor(k): … }` —
  preferred over a pattern-match definition.
- `by_induction on n with IH refining h1, h2 { … }` — also refine
  the listed in-scope binders' types per case (so hypotheses about
  `n` get the right shape in each arm).
- `by_induction on n using <strongRecursionLemma> { … }` — route
  the recursion through a user-supplied recursion principle.
- `by_strong_induction on n with IH { … }` — strong induction on a
  Natural; IH has type `(k : Natural) → k < n → P(k)`.

`done` and `okay` are aliases for `claim goal` — pick whichever spells
the proof's intent: "the proof is done here" (`done`), "okay, that proves
it" (`okay`), or the explicit `claim goal by …`. (`goal` on its own is
just the name of the goal type, not a closer.)

The remaining subsections are about *CIC noise* — bureaucracy that
the kernel demands but a mathematician would never write. Those
should be hidden behind named helpers; the rules below collect the
ones that come up most often. None of these rules trade away
readability — they only remove ceremony.

### `<order>.weaken` over `And.left` on a `<` hypothesis

`Rational.LessThan(x, y)` unfolds to `And(LessOrEqual(x, y),
Not(x = y))`. With `h : x < y` and a goal needing `x ≤ y`, prefer

```math
Rational.LessThan.weaken(x, y, h)         -- 1 line
```

over

```math
And.left(Rational.LessOrEqual(x, y), Not(x = y), h)   -- 3-5 lines
```

Same for `Rational.LessThan.distinct(x, y, h) : ¬(x = y)` vs
`And.right(...)`. Helpers live in `Rational/order_arithmetic.math`
alongside `LessOrEqual.negate`, `LessThan.negate`,
`negate_LessThan_zero_of_positive`, `LessOrEqual_zero_of_negate_IsNonneg`.

### Quarantine the machinery: layer the file

Keep proof-assistant bureaucracy out of the mathematical proof by giving
the file a consistent layering:

    definition / construction     -- the object
    boundary lemmas               -- the only way in and out of the encoding
    representation-level kernel    -- the math, stated in boundary terms
    thin adapter (if needed)      -- bridges the encoding to the kernel
    public theorem

The discipline that makes this pay off, for an **opaque quotient** like
`Integer` (the difference-class quotient of `IntegerRepresentative`):

- **Every lifted operation publishes a representative-computation boundary
  lemma.** `Integer.from_difference_times_natural : from_difference(p, q) ·
  (c : Integer) = from_difference(p·c, q·c)` lets a consumer scale a
  difference *at the boundary* instead of unfolding the `multiply` lift at
  representatives. Without it the proof drowns in `make(p·c + q·0, …)` noise.

- **Consumers compare quotient values only through the boundary lemmas**
  (`difference_equal` / `difference_equal_implies`), never
  `Quotient.class_of` / `.equivalent_implies_equal` /
  `.equal_implies_equivalent` directly. Those are construction-internal.

- **State the mathematical lemma in boundary terms; quarantine the quotient
  `cases` bridge in a thin adapter.** In `Integer/cancellation.math` the
  heart is `multiply_cancel_right_at_differences`, proved purely in
  `from_difference` — no `Quotient.class_of` in sight; a one-line
  `*_at_representatives` adapter bridges what `cases` produces to it. The
  math reads clean and the maintainer still sees where induction enters.

- **Name vacuous / structural constructions behind the concept.** A
  bijection between two empty types is `Equinumerous.empty_types`, not a
  nested `⟨absurd(…), ⟨absurd(…), …⟩⟩` at the use site. Likewise maps out
  of `False`, identity inverses, subtype proof-irrelevance.

The smell: if a *consumer's* proof mentions the encoding (`Quotient.class_of`,
a raw `make(…)` rep, an `unfold <Opaque>`), a boundary lemma is missing — add
it next to the operation, not a workaround at the call site.

### Pattern-match at constructor reps for Quotient-lifted proofs

The bad shape (~80 lines): `Quotient.induct_two` whose at-rep body
threads bridge lemmas (`sequenceFunction_add`, etc.) through a calc
chain to reach a pointwise Rational fact.

The good shape (~20 lines): a separate `*_at_make` theorem that
pattern-matches the reps to expose the underlying sequences, plus a
top-level `Quotient.induct[_two|_three]` lift. When the rep is in
constructor form, the kernel's β/ι reduces every
`sequenceFunction(add(make(sx, _), make(sy, _)), n)` to
`sx(n) + sy(n)` and the bridge proofs become reflexivity.

```math
theorem Foo_at_make
        : (rep_x rep_y : CauchyRationalSequence) → … (Quotient.mk rep_x) … (Quotient.mk rep_y) …
  | CauchyRationalSequence.make(sx, sx_cauchy),
    CauchyRationalSequence.make(sy, sy_cauchy) ↦
      Quotient.sound(…, …, (n : Natural) ↦ Rational.foo(sx(n), sy(n)))

theorem Foo (x y : Real) : … :=
  Quotient.induct_two(motive, Foo_at_make, x, y)
```

Caveat: when the at-make body needs to refer to a rep AGAIN
(typically when passing it to `Quotient.sound` or
`equivalent_when_sequenceFunction_equal`), the pattern wildcards must
each have a fresh NAME (`sx_cauchy`, `sy_cauchy`). Using `_` makes
the kernel re-bind a single fresh variable and the Cauchy proofs
collapse to the wrong type.

### Avoid auxiliary `CauchyXxx` definitions for one-off proofs

A standalone `definition CauchyRationalSequence.foo_residual : … →
CauchyRationalSequence` plus a `sequenceFunction_foo_residual`
bridge lemma is almost always a red flag — pattern-matching at make
inside an `at_make` theorem subsumes it without the auxiliary
definition. A previous draft of the triangle-inequality proof spent
200 lines on this pattern; the at-make refactor took 40.

## `--goal-at` — ask what the goal is at a line

A poor man's infoview: when you are mid-proof and unsure what remains to
be proven (or what hypotheses are in scope), put a `sorry` where you are
stuck and query its line:

```
./kernel verify --source <file>.math --cache-root build --goal-at <line>
```

It prints the hypotheses and goal at the proof statement at (or nearest
before) that line — pointing anywhere inside a multi-line statement
reports the enclosing statement:

```
goal at line 147:
  divisor : Natural
  dividend : Natural
  remainderBelowDivisor : successor recursedRemainder ≤ divisor
  bumpedDecomposition : dividend = (successor recursedQuotient) * divisor + recursedRemainder
  ⊢ Natural.has_quotient_remainder divisor dividend
```

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
auto-prover closes the step/claim without the hint) and an *unused-name*
finding (a binding the prover consumes by type-match, so the name is dead
weight). `.mark_redundant.py <files>` annotates the calc-step `by` sites
with marker
comments; you then **edit by hand and rebuild**, reverting anything that
turns out to be load-bearing (the checker tests each site in isolation, so
adjacent steps in a chain can interact). Do NOT write a fully-automated
rewriter.

**How to resolve each finding — by readability, not by chasing zero:**

- **Redundant `by` on a *calc step* citing a library lemma / tactic**
  (`by ring`, `by add_successor`, `by multiply_commutative`) → make it
  **by-less**. The calc already shows the intermediate form; the citation
  was noise.
- **Redundant `by` on a *claim* that names the operative lemma** (often
  with a long positional argument list) → rewrite as argument-free
  **`since <Lemma>`**. `since` names the insight, drops the clutter, and is
  *exempt* from the redundant-`by` check (it signals "the author is
  explaining"). Prefer this over baring the claim, which would read as an
  unexplained assertion.

**The cascade — expect it, and settle it.** Removing a `by` (or going
argument-free) makes the auto-prover pick the needed fact out of context by
*type-match* instead of by name. Two follow-on findings appear:

1. A named intermediate `claim NAME : T by …` whose `NAME` is now only
   consumed by type-match → flagged **`unused name`**. Fix: **anonymize**
   it — `claim T by V;` (or bare `claim T;` if its own `by` was also
   redundant). The fact is still stated and still in context for the
   type-match; only the dead label goes. Keep a name **only** when it is
   referenced by name later (a genuine milestone).
2. A calc step that fed such a claim may itself become redundant → by-less
   it too.

Re-run the check after editing; the cascade is finite and converges to
by-less routine steps + anonymous intermediate facts + `since`-cited
operative lemmas. Stop short of churning when removal would *worsen*
things: by-less'ing a step that cites an `obtain`/`suppose` binder just
moves the warning to an "unused binder" (use `as _`, or leave it); and a
genuinely informative reduction *chain* in a `calc` is worth keeping even
when the prover could skip it.

**`by` vs `since` vs `note` — the mnemonic.** `by` = the prover needs it.
`since` = a kept explanation the prover does *not* need (exempt from the
redundant-`by` check). `note P [by …];` = a verified comment that is **not
added to the context** — so never use `note` for a fact a later step must
consume by type-match (it won't be there); use an anonymous `claim` for
that.

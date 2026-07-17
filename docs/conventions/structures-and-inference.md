# Structures, conventions, and inference

Name-bound `convention`s, implicit arguments `{x:T}`, canonical `instance` inference, and operator overloading (incl. the `·`/postfix `⁻¹` group operators).

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

## Name-bound conventions

`convention p [q ...] : T [with H1 [, H2 ...]];` at the file top
registers a name as an auto-prepended implicit binder. Mirrors the
math-book "throughout this chapter, p and q denote prime numbers"
convention.

```math
convention p : Natural with Natural.is_prime(p)

-- Subsequent theorems mentioning `p` get
-- {p : Natural} {_ : Natural.is_prime(p)} prepended implicitly.
theorem prime_self_divides : p ∣ p :=
  ⟨successor(zero), ...⟩
```

Notes:
- No semicolon at the end (matches other top-level declarations).
- If the user shadows the convention name with their own binder, the
  convention does NOT fire for that declaration.
- Conventions fire on `definition` and `theorem`. Inductive
  declarations and axioms are not covered.
- Call sites still rely on the existing implicit-arg machinery —
  arguments uniquely determined by another argument's type are
  inferred; purely propositional arguments may need to be passed
  explicitly.

## Implicit arguments

`{x : T}` binder syntax is supported on `definition`, `theorem`, and
`axiom`. Use this when a parameter is determined by another's type:

```math
theorem refl_implicit {T : Type(0)} (x : T) : x = x :=
  reflexivity(T, x)

-- Call site doesn't pass T:
refl_implicit(n)  -- T inferred as Natural
```

PAdic operations currently thread `(p : Natural) (primality :
Natural.is_prime(p))` explicitly. If you're writing NEW PAdic code,
consider making them implicit: `{p : Natural} {primality :
Natural.is_prime(p)}`. Existing PAdic code uses explicit form for
historical reasons; migration is a planned cleanup.

## Canonical instances — `instance` and instance inference

`instance <name>` registers a theorem that proves a structure predicate
(`IsMonoid` / `IsGroup` / `IsRing` / …) as the **canonical instance** for
its `(structure, carrier)` pair. A generic lemma whose structure,
operation, and instance arguments are *implicit* then has them filled
from the registry at concrete call sites — keyed by the carrier head.

```math
instance Integer.add_is_group   -- registers (IsGroup, Integer)

theorem cancel_left_inferred
        {carrier : Type(0)}
        {operation : carrier → carrier → carrier}
        {identity : carrier}
        {inverse : carrier → carrier}
        {groupProof : IsGroup(carrier, operation, identity, inverse)}
        (a b c : carrier)
        (equation : operation(a, b) = operation(a, c))
        : b = c := …

-- Concrete call: carrier (from `a`) and operation (from the `+` in the
-- equation) come from the explicit args; identity / inverse / groupProof
-- are read off the registered `Integer.add_is_group` instance. No
-- ceremony arguments.
theorem integer_cancel (a b c : Integer) (equation : a + b = a + c)
        : b = c :=
  cancel_left_inferred(a, b, c, equation)
```

Resolution rule (mirrors the coercion registry): **at most one instance
per `(structure, carrier)`**. Registering a second is rejected with a
diagnostic — never guessed, never backtracked.

Parameterized carriers work too. An instance whose type is Pi-quantified
(`IntegerMod.add_is_group (modulus) : IsGroup(IntegerMod(modulus), …)`)
registers under the carrier head (`IntegerMod`); at a call site over
`IntegerMod(m)` the leading parameter is instantiated from the carrier's
own argument `m`, threading `IntegerMod.add_is_group(m)` automatically.

Abstract carriers work via **local-instance search**: when the carrier is
not a concrete head but the call site has a UNIQUE in-scope hypothesis of
the right structure, that hypothesis is used as the instance (and its
operations read off to fill the siblings). This is what lets a generic
lemma consume another over its own abstract carrier with no ceremony —
e.g. `Ring.zero_multiply` calls `Group.cancel_left(0·x, 0·x, 0, eq)` and
the `IsGroup` instance is resolved from the ring's derived
`addGroupProof` already in scope. A non-unique match is rejected (not
guessed), same stance as the registry.

What instance resolution will NOT touch (by design):
- **Ordinary value predicates** like `Natural.is_prime(p)` or
  `Natural.divides(a, b)`. The gate fires only on a *structure class* —
  a Proposition-valued head whose FIRST parameter is a carrier *type*
  (`IsGroup(carrier, …)`), not a value (`is_prime` takes a `Natural`).
  Side-condition proofs like `primality` stay explicit.
- For carriers the `ring` / `field` tactics already cover, prefer those —
  instance inference is for hand-cited structure lemmas they can't
  discharge (cancellation, inverse-uniqueness, …).

## Operator overloading

`operator (sym) on (T1, T2) := F;` registers `sym` to dispatch on
the *heads* of T1 and T2 — `PAdicCauchySequence`, `Ring.carrier`, etc.
A parameterized head like `PAdicCauchySequence(p, primality)` is fine:
the dispatcher recovers the structure indices (`{p}`, `{primality}`,
or a `{r : Ring}` projected out of `Ring.carrier(r)`) from the operand's
type — the implicit-recovery mechanism pinned by
`Test/operator_parametrized_poc.math`. So:

- `operator (+) on (Integer, Integer)` works.
- `operator (*) on (CauchyRationalSequence, …)` and
  `operator (*) on (PAdicCauchySequence, …)` work: `a * b` recovers any
  index (e.g. the prime `p` on the p-adic type) from `a`'s type, so the
  underlying `…multiply` need not be given `(p, primality)` by hand.
- `operator (∣) on (Ring.carrier, Ring.carrier) := Ring.divides` lets `p ∣ a`
  recover the ring `s` from `p : Ring.carrier(s)` — exactly as `+`/`*` do.
  `∣` is an ordinary registry operator (per type), **not** a built-in: it is
  registered `on (Natural, Natural)` and `on (Ring.carrier, Ring.carrier)`, so
  `∣` works for any type that registers it, with no elaborator special case.
- The one requirement is that those structure indices be *implicit* on
  the dispatch function `F` (`{p}` not `(p)`), so `F` is callable as
  `F(a, b)`; the `convention`-prepended `{p}`/`{primality}` satisfy this.

### Application: `operator (()) on (T) := F`

A value that *wraps* a function can be registered to apply directly:
`operator (()) on (CauchyRationalSequence) := CauchyRationalSequence.sequenceFunction`
lets a proof write `rep(n)` for the n-th term of the packaged sequence,
and `operator (()) on (Permutation) := Permutation.apply` lets it write
`sigma(i)` (and `(rep_x * rep_y)(n)`, `sigma(sigma(i))`, …). Elaborating
`f(a)` where `f`'s type is a non-function whose head has a registered
`()` dispatches to `F(f, a)` — the emitted term is byte-identical to the
spelled-out call, so citations, matchers, and defeq are unaffected. `F`
must take the wrapped value as its first explicit argument and return a
function (`T → (A → B)`); implicit indices (`Permutation.apply`'s `{n}`)
are recovered from the value's type as with any operator.

## Citing a lemma by name — let the arguments be inferred

A lemma cited as `by <Lemma>` (no argument list) has its arguments filled
from the goal and the local context, so you rarely spell them out:

- **Goal-driven**: arguments fixed by the lemma's conclusion are read off
  the goal. `claim a + 0 = a by add_zero` → `add_zero(a)`.
- **Discharged from context**: a remaining *proof* premise is matched
  against an in-scope hypothesis (or a `recalling`-listed fact). This is
  how an inequality/divisibility lemma whose premises already sit in scope
  closes with no arguments.
- **Match-and-unify**: a premise can *also* solve a value the conclusion
  didn't pin. `Polynomial.HasDegree_unique`'s conclusion is `d = e`, so it
  leaves the ring `r` and polynomial `p` open; unifying its
  `HasDegree(r, p, d)` premise against a local `HasDegree(Real.ring, q, d)`
  fact solves `r` and `p` as a side effect. Search is bounded to the local
  context + recalled facts — never a global proof search to fill an
  argument.
- **Back-inference (args only in hypotheses)**: this runs to a *fixpoint*,
  so a lemma whose key arguments never appear in its conclusion is still
  citable by name. `NaturalList.all_prime_under_prepend_equality`'s
  conclusion is just `is_prime(candidate)`; citing it recovers everything
  else from the hypotheses — `member(candidate, list)` matched against the
  local `membership` pins `list`, `is_prime(head)` / the all-prime-tail
  premise pin `head` / `tail`, and the leftover equality premise
  `list = prepend(head, tail)`, now fully determined, is discharged by
  **reflexivity**. So `:= claim by NaturalList.all_prime_under_prepend_equality`
  replaces an eight-argument call.
- **Conjunction-conclusion projection**: a cited fact whose conclusion is
  `A ∧ B` proves a goal matching ONE leg — `P(m) by h` works for
  `h : ∀ (k : Natural). P(k) ∧ Q(k)`; the citation instantiates the fact
  and wraps the matching projection, so the unused leg never reaches the
  page.

```math
claim productHasDegree : Polynomial.HasDegree(Real.ring, a * b, da + db)
  by Polynomial.HasDegree_product
      recalling Real.multiply_commutative, Real.reciprocal_exists_for_nonzero
```

`recalling f, g` brings extra named facts into that discharge scope as
bounded, context-local hypotheses (no global library scan) — use it for a
lemma's "dictionary" premises (a ring's commutativity / inverse witnesses)
that aren't local hypotheses. A partial call leaves the rest as holes:
`HasDegree_unique(Real.ring, modulus, d, 2, ?, ?)`.

Named and anonymous claims elaborate through the **same** path, so all of
the above works identically in `claim NAME : T by …` and `claim T by …`.

## Citing a fact (a proposition) where a proof is expected

A parenthesised **proposition** written where a proof is expected — e.g.
`by (1 ≤ 1 + n)` — is **auto-proved**, and the synthesized proof is then
handled identically to a user-supplied proof of that proposition. One
primitive, three positions:

- **proof position** — `… ≤ b by (x ≤ y)` on a chain step, or `P by
  (<fact>);`. The proof of the cited fact bridges to the goal by the same
  paths as `by <proof>`: definitional match, conclusion-unify, and the
  diff/congruence bridge (so `succ(a) = succ(b)` closes from `by (a =
  b)`). It does **not** chain through a combining lemma or flip by
  symmetry — the cited fact's proof must *directly* establish the goal.
- **recalled-fact position** — `by <lemma> recalling (<fact>)`. The fact
  is auto-proved into the lemma's discharge scope, so a premise the
  ambient context doesn't supply is met without writing its proof term.
  This is how a combining lemma's stepping-stone premise is supplied:
  `… ≤ … by add_general_LessOrEqual_left recalling (0 ≤ n)`. (Contrast
  `recalling Natural.zero_least(n)` — the explicit proof-term form.)
- **substitution equation** — `by substituting (a = b)`: the equation is
  cited as a bare proposition, auto-proved, then used to rewrite the
  goal. (`by substituting <eqProof>` still accepts a proof.)

Mnemonic: `by (<fact>)` names the **fact** and lets the prover find the
lemma; `by <lemma> recalling (<fact>)` names the **lemma** and supplies
the fact for its premise. Prefer the former when a single simple fact
carries the step; reach for the latter when a combining lemma is needed.

## The verified comment: `note`

See `proof-style.md`. In short: `note P [by V];` is a `claim` that does
*not* add the fact to the context (a verified comment), so it's outside
both the unused and redundant checks. (`since <proof>` — formerly the
redundancy-exempt spelling of `by` — was removed from the language
(2026-07-02) and no longer parses.)

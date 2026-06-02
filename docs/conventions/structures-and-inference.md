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
- v1 fires on `definition` and `theorem`. Inductive declarations and
  axioms are not yet covered.
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
the heads of T1 and T2. T1 and T2 must be the heads of types, not
parameterized type applications. So:

- `operator (+) on (Integer, Integer)` works.
- `operator (+) on (PAdic, PAdic)` would conceptually work but
  `PAdic.add` takes `(p, primality, x, y)`, not `(x, y)`. Once `(p,
  primality)` become implicit on `PAdic.add`, the operator overload
  will work.

# Plan: implicit coercions for mixed-type arithmetic

**Vision.** A user writing real analysis should be able to write `x - 1 > 0`
for a real `x`, or `q + x` for a rational `q` and a real `x`, without
spelling out `(1 : Real)` or a `Rational.to_real` cast. The type of every
expression stays **computable bottom-up** — context-independent, as in C,
never Perl's scalar-vs-list ambient context. The only thing that changes is
the *result-type function* of a binary operator: instead of requiring the
two operand types to be equal, it takes their **join** in a partial order of
canonical coercions and runs the operator there.

The coercions only ever go **up** an order of injective,
structure-preserving maps (`Natural ↪ Integer ↪ Rational ↪ Real ↪ Complex`),
so a named variable is never silently demoted and nothing surprising can
happen at a genuine type mismatch: the only reconciliation available is the
safe, information-preserving one.

## Why a join-semilattice (and where it stops)

The coercion structure of the concrete number tower is a join-semilattice —
a partial order in which any two combinable types have a unique least upper
bound. It stays one even when it stops being a chain: two incomparable
completions of `ℚ` (`Real` and a future `PAdic p`) have **no** common upper
bound, and that is *correct* — adding a real to a p-adic should be an error,
and partiality of the join lands the error exactly there.

It does **not** scale to all of mathematics, and we accept that up front:

- **Non-injective casts** (`Integer → IntegerMod n`) break the "up is
  always safe" property. These stay **explicit**; they are never registered
  as auto-coercions.
- **Parameterized types** (`Polynomial(R) + S → Polynomial(join(R,S))`) make
  the join a *pushout* the elaborator would have to construct, not a table
  lookup. Out of scope for the string-keyed registry; deferred to the
  heterogeneous-operator tier below.
- **Field compositums** have no canonical join at all (it depends on an
  ambient embedding). No common-type rule can serve these; the maps are
  explicit, named embeddings.

This mirrors where Mathlib landed: it does *not* minimize casts at parse
time via a common-type rule. It uses heterogeneous operations (`HMul α β γ`),
scalar actions (`SMul`), and after-the-fact cast normalization
(`push_cast`/`norm_cast`). Our design reaches the same destination, more
cleanly typed: a join-semilattice for the injective number core, a
heterogeneous-operator tier for structured combinations, and explicit maps
for the lossy / non-canonical rest.

## What already exists

Two-thirds of Tier 1 is already built:

- **A coercion partial order.** `coercion (S, T) := F;` populates
  `environment_.coercionRegistry : (srcHead, tgtHead) → [funcName...]`
  (`kernel.hpp:153`). `elaborateCoercionDeclaration`
  (`statements.cpp:430–546`) **transitively closes** the registry at
  registration (`statements.cpp:472–519`) and **rejects diamonds**
  (`statements.cpp:520–540`). So `(Natural, Real) → [to_integer,
  to_rational, to_real]` is a single lookup and the path is provably unique.
  This registry *is* the semilattice's edge set with all paths precomputed.
  Declarations live in `library/Integer/embedding.math:30`,
  `library/Rational/embedding.math:42`, `library/Real/embedding.math:39`.

- **Chain application.** `dispatch.cpp:1547–1553` wraps an expression in a
  coercion chain — but **only at ascription sites** `(expr : T)`. That is
  the entire current story: coercions fire when you explicitly ascribe,
  never at an operator.

The gap is a single thing: `desugarArithmeticOperator`
(`desugar_equality.cpp:9`) requires operand heads to already match. It
synthesizes `leftHead` (`:114`) and `rightHead` (`:123`), then calls
`lookupOperator(sym, leftHead, rightHead)` (`:124`). Nothing registers `+`
on `(Rational, Real)`, so mixed operands miss the registry and error. The
fix is a **join step between synthesizing the heads and the registry
lookup**.

## The `Combine` interface

Operand reconciliation is factored behind one function so that Tier 1 is a
*provider*, not hardcoded logic — the single architectural commitment that
lets Tiers 2–3 slot in later without a rewrite.

```cpp
struct CombineResult {
    ExpressionPointer        resultType;      // C — the type the operator runs at
    std::vector<std::string> coerceLeft;      // chain A → C  (empty if A == C)
    std::vector<std::string> coerceRight;     // chain B → C  (empty if B == C)
    std::string              operatorOverride;// Tier 2 only; "" for Tier 1
};

// Each provider either handles (leftHead,rightHead) or declines (nullopt);
// the next is tried. Order encodes precedence.
std::optional<CombineResult> combineOperands(
    const std::string& opSymbol,
    ExpressionPointer leftType,  const std::string& leftHead,
    ExpressionPointer rightType, const std::string& rightHead);
```

Providers, in order:

1. **Homogeneous** — `leftHead == rightHead` (or defeq): `C = leftType`,
   both chains empty, no override. The current fast path, unchanged.
2. **Tier 1 — semilattice join** over `coercionRegistry` (algorithm below).
   Coerce the lower operand up to the join.
3. **Tier 2 — heterogeneous registry** *(future, not built now)*: a
   `hetero_operator (sym) on (A,B) := F : A→B→C` returns `C` with empty
   coercion chains and `operatorOverride = F`. Home of `r • v`, scalar
   actions, and eventually `Polynomial(ℝ)·ℂ → Polynomial(ℂ)`.
4. **No provider → error**, naming both types and suggesting an explicit
   cast. Tier 3 *is* this case: the user writes the map by hand.

`desugarArithmeticOperator` calls `combineOperands` and never mentions
`join` directly.

## The join algorithm (Tier 1)

```
reach(A,B):  A==B → []        ; else registry[(A,B)] if present ; else ⊥

join(A,B):
  if reach(A,B) ≠ ⊥:  return (C=B, coerceLeft=reach(A,B), coerceRight=[])   # A ≤ B
  if reach(B,A) ≠ ⊥:  return (C=A, coerceLeft=[], coerceRight=reach(B,A))   # B ≤ A
  # incomparable — search for a least common upper bound:
  uppersA = {A} ∪ { X : reach(A,X)≠⊥ };  uppersB = {B} ∪ { Y : reach(B,Y)≠⊥ }
  commons = uppersA ∩ uppersB
  if commons = ∅:        return ⊥        # Real vs PAdic → error, correctly
  least = { C∈commons : ∀C'∈commons, C==C' ∨ reach(C,C')≠⊥ }
  if |least| == 1:       return (C, reach(A,C), reach(B,C))
  else:                  error "ambiguous common type for A, B — cast explicitly"
```

- For the **linear tower** the first two lines always fire (`join = max`);
  the incomparable search never runs. It exists for forward-compat and
  produces exactly the partiality we want: incomparable branches → clean
  error, never a silent coercion.
- Diamond-freedom is **already enforced** at registration, so `reach(A,C)`
  and `reach(B,C)` are unique chains. The only residual ambiguity is *which
  target*, caught by the `least` check.
- It only ever coerces **up** (registry edges are the injective inclusions),
  so the no-surprise property holds.

## Two hook sites (not one)

`=` is desugared **separately** from arithmetic operators —
`dispatch.cpp:1571–1600` builds `Equality.{u}(leftType, a, b)` off the left
operand's type, so `(n : Natural) = (x : Real)` currently forces
`Equality(Natural, …)` and fails. Both sites route through `combineOperands`:

- **`dispatch.cpp:1571`** — compute `join(leftType, rightType)`, coerce both
  sides, build `Equality(C, …)`.
- **`desugar_equality.cpp:124`** — compute the join, apply
  `coerceLeft`/`coerceRight` to `leftKernel`/`rightKernel`, then
  `lookupOperator(sym, Chead, Chead)`.

Lift the chain-application loop from `dispatch.cpp:1547–1553` into a shared
helper `applyCoercionChain(expr, chain)` used by both the ascription path
and the new operator path.

**Checked:** the right operand is elaborated with the left's type as
expected (`desugar_equality.cpp:107–109`), but this does **not** pre-coerce
— registry coercion fires only in the ascription branch, and the general
expected-type path (`coerceToExpectedTypeViaDiff`) does diff/equality
bridging, not numeric casts. So both operands' synthesized heads are their
true types, and the join fires correctly and symmetrically on `x + q` and
`q + x`. The literal case (`x - 1`) works too: `1` synthesizes as `Natural`
and rides the chain up to the real-typed operand's join.

## Coherence lemmas Tier 1 owes

The registry guarantees *syntactic* path-uniqueness — enough to
**elaborate** `x - 1 > 0`, but not to **reason** about the result. For
proofs to manipulate coerced expressions we owe the `norm_cast` lemma
families, per coercion `ι : A → C`:

1. **Homomorphism** — `ι(a ⊕ b) = ι(a) ⊕ ι(b)` for `+`, `*`, and
   `ι(0)=0`, `ι(1)=1`. (Mostly already present — they make the embeddings
   meaningful.)
2. **Order / injectivity reflection** — `ι(a) ≤ ι(b) ↔ a ≤ b` and
   `ι(a) = ι(b) ↔ a = b`. These discharge a coerced (in)equality at the
   source type and formally back the no-surprise claim.
3. **Composite normal form** — a recognized form for
   `to_rational(to_integer(n))`, so a `norm_cast`-style normalizer can
   cancel stacked casts.

Tier 1 ships without a `norm_cast` tactic, but the casts the join *inserts*
are exactly the ones a proof then pushes around — so **build the
`push_cast`/`norm_cast` normalizer as the immediate Tier-1.5 follow-on**,
fed by these lemma families.

## Known limit (on the record)

The registry key is `(string, string)` — bare head names. It **cannot**
express `join(Polynomial(R), S) = Polynomial(join(R,S))`. Parameterized-type
pushouts are deliberately out of scope for this key structure; when they
arrive they go through the Tier-2 heterogeneous provider with a functorial
rule, not a registry row. String-keyed join is the concrete-tower solution,
not the universal one.

## Milestones

1. **Design** — this document.
2. **Tier 1** — `combineOperands` (homogeneous + join providers),
   `applyCoercionChain` helper, both hook sites wired. Validate with a clean
   `make tests` and `x - 1 > 0` / `q + x` cases.
3. **Tier 1.5** — `push_cast`/`norm_cast` normalizer + the coherence-lemma
   audit (which homomorphism/injectivity lemmas already exist in
   `Integer`/`Rational`/`Real` embeddings vs. what is missing).
4. **Library sweep** — delete now-redundant explicit casts across the
   analysis cone; measure the noise reduction.
5. **Tier 2** *(deferred)* — heterogeneous-operator registry for scalar
   actions and parameterized-type combinations.

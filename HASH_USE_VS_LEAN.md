# How our subtree-hashing plan compares to Lean's hash usage

Background: TODO.md "subtree hashing for the auto-prover" (Phases 1–3)
is in flight. Lean uses hashes pervasively but in shapes that differ
from each of our planned phases. This note pins down where we line up
and where we diverge, so we know what Lean docs/code transfer and what
doesn't.

## 1. Per-node cached structural hash → fast-reject in equality

**Same as Lean.** Our Phase 1 — `uint64_t hash` on `Expression` /
`Level`, populated in the `make*` helpers, used as a fast-reject before
recursive structural compare — is essentially what Lean's `Expr.hash`
field does. Lean computes it in its smart constructors and uses it
identically: structurally-unequal hashes prove structurally-unequal
terms, which prunes `isDefEq` and other recursion.

## 2. Hash-consing / maximally-shared expressions

**Lean's *primary* use of hashes; we are not planning this yet.** In
Lean (Lean 3 always-on; Lean 4 via the dedup tables consulted by
`mkApp`/etc.), constructing a structurally-identical expression returns
the *same pointer*. The cached hash drives the bucket lookup in that
dedup table. Once dedup is in place, "structurally equal" collapses to
"pointer-equal," and every downstream pass (`whnf`, `instantiate`,
`abstract`, `inferType`) memoizes by pointer for free.

We get partial credit today — `structurallyEqual` (kernel.cpp:618) and
`isDefinitionallyEqual` (kernel.cpp:690) both short-circuit on pointer
identity — but we don't actively create the sharing. At current scale
(0.3s cold rebuild) it doesn't bite; at 10× library size it would.
Adopting dedup is the natural extension of Phase 1: same hash, a bit
more bookkeeping in the constructors.

Side benefit Lean gets from this that we don't: Lean caches
`hasFVar`, `hasMVar`, `hasLooseBVar`, and `looseBVarRange` per `Expr`
alongside the hash. These let `instantiate` / `abstract` / substitution
skip whole subtrees in O(1) when they obviously contain nothing to
rewrite. Worth picking up regardless of whether we ever do dedup —
the bits ride alongside the hash, populated in the same `make*`
helpers, and would make `openBinder` / `closeBinder` / `substitute`
O(1) on closed subterms.

## 3. AC-modulo equality (our Phase 2)

**Lean does *not* do this anywhere.** Lean's kernel treats `a + b` and
`b + a` as definitionally distinct; their equality is propositional and
proved by `add_comm`. AC reasoning lives entirely in tactics — `ring`
normalizes both sides to a canonical polynomial form and emits an
explicit proof term using `mul_comm`, `mul_assoc`, etc.; `simp [ac]`
likewise emits explicit rewrites.

Our Phase 2 makes the *auto-prover* (an elaborator-level component)
hash modulo AC, then verifies via the kernel by emitting the explicit
lemma. That's sound — the kernel never sees AC-modulo equality — but
the underlying technique is closer to an e-graph / egg-style
equivalence-class hash than to anything Lean does. Defensible design;
just don't expect Lean code or docs to look like guidance for it.

Hazard to watch: hashing modulo AC under binders requires care so that
`λx. x+y` and `λx. y+x` collide but `λx. x+y` and `λx. x+z` don't.
Multisets keyed by subtree hash do the right thing if the AC chain is
flattened *and* bound variables remain pinned to the same de-Bruijn
slot. The TODO.md note about "AC-flattening under binders" is the
right thing to be nervous about.

## 4. Theorem-shape indexing (our Phase 3)

**Lean does this, but with *discrimination trees*, not hashes.**
`Lean.Meta.DiscrTree` keys each lemma by a depth-first sequence of
head symbols (with wildcards for metavariables). Lookup walks the goal
in the same order, pruning on the first head mismatch. `simp`,
`rewrite`, `apply?`, typeclass resolution, and `library_search` all
use them.

Why Lean doesn't use hash-bucket indexing for this: hashes give
exact-shape match in O(1), but lemmas have *metavariables*
(`∀ a b c, (a + b) + c = a + (b + c)` matches against any
`(?a + ?b) + ?c`). Hash buckets can't represent that without a
separate wildcard slot, which forces a fallback to linear scan.
Discrimination trees encode wildcards natively as a branch.

What Phase 3 buys at lower cost: if we hash the *AC-canonical* form
(Phase 2's `acHash`) and lemma LHSs are also hashed in canonical form,
we get AC-tolerant exact-match for closed-LHS rewrites — commutativity,
associativity, identity, and distributivity-after-canonicalization.
That covers most of the calc-step boilerplate the audit flagged, *as
long as* a lemma's metavariables are all in argument position (so the
canonical hash treats them as fresh leaves consistently). For real
unification-style matching (`f(?x, g(?x))`) we'd still need a small
one-way matcher *after* the hash-bucket prefilter — which Phase 3's
plan already specifies.

So Phase 3 is reasonable as a cheap first cut; graduating to
discrimination trees becomes attractive once the lemma corpus is big
enough that hash collisions in wildcard space start mattering.

## 5. Packing the cached metadata into the hash word

If we adopt the `hasFreeVariable` / `hasLooseBoundVariable` /
`looseBoundVariableRange` metadata (point 2 side benefit), we can keep
the per-node footprint at one 64-bit word by stealing the high 8 bits
of the existing `uint64_t hash` field instead of adding a separate
flags field.

Hash-quality cost of truncating from 64 bits to 56 bits:

- FNV-1a 64-bit: birthday collisions at ~2^32 terms ≈ 4B.
- FNV-1a 56-bit: birthday collisions at ~2^28 terms ≈ 268M.

Library scale is 10^5–10^6 expressions live at peak — five orders of
magnitude under the 56-bit regime. And in every use of the hash, a
collision is correctness-preserving:

- Phase 1 fast-reject: collision → recursive `structurallyEqual`. Sound.
- Phase 2 AC-canonical: collision → falls through to kernel verification
  of the emitted proof. Sound.
- Phase 3 lemma indexing: collision → bucket has 2 candidates, matcher
  runs twice. Bounded by lemma-corpus size.

Suggested 8-bit allocation:

| Field | Bits | Notes |
|---|---|---|
| `hasFreeVariable` | 1 | True if subtree contains any User-origin FreeVariable |
| `hasLooseBoundVariable` | 1 | True if subtree contains a BoundVariable below the local cutoff |
| `looseBoundVariableRange` | 6 | Max loose-bvar index + 1, saturated to 63 |

Saturation at 63 is fine — our binders rarely nest that deep, and any
subtree past the saturation just doesn't get the O(1) skip in
`shift` / `substitute` / `openBinder`.

Layout:

```cpp
// Low 56 bits: structural hash. High 8 bits: metadata.
uint64_t hashAndFlags;

static constexpr uint64_t kHashMask   = (1ULL << 56) - 1;
static constexpr int      kRangeShift = 56;          // 6 bits
static constexpr int      kFlagHasFreeVarBit          = 62;
static constexpr int      kFlagHasLooseBoundVarBit    = 63;
```

Hash combine in the `make*` helpers operates on the masked low 56 bits.
Flags combine separately: `hasFreeVariable` and `hasLooseBoundVariable`
propagate up via OR over children; `looseBoundVariableRange` propagates
as `max(child_ranges adjusted by binder offset, 0)` saturated at 63.

Why pack instead of using a separate field: `Expression` is already
~96 bytes (the `std::variant` dominates at ~80 bytes plus tag and the
hash word). A separate `uint8_t flags` field would round up to +8 bytes
with alignment. Packing costs zero bytes and adds one mask/shift per
read, invisible against the cost of `make_shared`.

The only reason to *not* pack is if we ever wanted to export the hash
externally (cross-process dedup table, serialized index). We're not
planning either, and FNV-1a isn't a hash we'd expose externally anyway.

## 6. Comparison table

| Use | Lean | Us (current / planned) |
|---|---|---|
| Per-node cached hash for fast-reject | yes | **Phase 1** |
| Hash-consing / dedup → pointer-identity everywhere | yes (primary use) | not planned |
| Cached `hasFVar` / `hasMVar` / loose-bvar metadata | yes | not planned |
| AC-modulo equality in the trusted base | no | not planned (would be unsound) |
| AC-modulo equality in the auto-prover | no (tactics emit explicit proofs from canonical forms) | **Phase 2** |
| Lemma indexing | discrimination trees | **Phase 3** (hash buckets, AC-canonical) |

## Bottom line

If we want one piece of Lean's approach that we don't have and can fold
into the in-flight Phase 1 work at low marginal cost, it's the cached
`hasFreeVariable` / `hasLooseBoundVariable` / `looseBoundVariableRange`
bits — same construction sites as the hash, and they make whole-subtree
skips in substitution/opening/closing O(1). We can keep the per-node
footprint at one 64-bit word by packing them into the high 8 bits of
the hash field (see §5); 56-bit hash is comfortably above our scale.

The dedup table (point 2) is a bigger commit and best deferred until
the bare hash has proved out in Phase 1 and we have a profile that
shows allocation-heavy hotspots.

Phase 2 is intentionally *not* Lean's approach. That's fine — `ring`
in Lean is a tactic, not a kernel feature, and we are explicitly
keeping AC-modulo reasoning out of the trusted base. Just don't expect
to find prior art in Lean for the hash-canonicalization choices.

Phase 3 trades expressiveness (metavariable patterns) for cheap
implementation. Worth knowing the discrimination-tree upgrade path
exists if/when hash-bucket collisions in wildcard slots become a
limit.

# Readability improvements — next round

Re-measured against commit `7b62d51` (2026-07-27), after the metric-topology
port and the interval migration. Every count below is reproducible with the
command given.

**This revises an earlier version written at `bea1113`.** Two of its six items
have since been done, one grew by half, and one new item appeared. The
"interaction with the interval change" section is deleted: that change landed.

The organising observation still holds. After three rounds of cleanup, almost
none of the remaining distance from "what a mathematician would write" is
*style*. It is the library writing down, by hand and thousands of times,
things a type system or an elaborator rule should insert.

---

## Already done — do not redo

| Was | State |
| --- | --- |
| Metric-space bundle; topology developed once | **done** (`Metric/`, 3,638 lines, 8 files; `Plane/*` are thin aliases). `PLAN_METRIC_TOPOLOGY.md` steps 0–3. |
| Curve domains → real interval | **done** (`7b62d51`). `Plane.IsArc (parametrisation : ℝ → Plane.Point)`. |

The interval migration paid in full:

```
Plane.unitSegment        279 → 0
Plane.walk                    → 0   (deleted)
Plane.Point.make(1, 0)   109 → 3
Plane.Point.first        565 → 114
```

The remaining 114 `Point.first` are all in `segment.math` (39), `point.math`
(10), `compact.math` (10), `norm.math` (9), `sequence.math` (9),
`model.math` (3) — genuine coordinates of genuine plane points, not parameter
unpacking. The ~18-lemma bridging vocabulary is down to 2. `Plane.retime` is
gone; `lowerHalf`/`upperHalf` are `Set(ℝ)`. `Plane/` is 7,606 lines, down from
9,027 at the first review while carrying substantially more mathematics.

---

## 1. Carrier and subtype coercions

**Promoted to first, and the case is now in-tree rather than hypothetical.**

```sh
for n in Ring.carrier NaturalsBelow.value MetricSpace.carrier VectorSpace.carrier \
         CommutativeRing.carrier Field.carrier Subtype.value NaturalsBelow.make; do
  printf "%-26s %5d\n" "$n" "$(grep -roh "$n(" --include=*.math library/ | wc -l)"
done
```

```
Ring.carrier                1125
NaturalsBelow.value         1097
MetricSpace.carrier          490      ← did not exist three commits ago
VectorSpace.carrier          404
CommutativeRing.carrier      300
Field.carrier                223
Subtype.value                185
NaturalsBelow.make           164
```

Roughly 3,990, up from ~3,900 at `bea1113` **despite** the interval migration
deleting 451 `Point.first` sites. The `MetricSpace` bundle added 490 on its own
(219 in signatures, 271 in proof bodies).

That is the argument. **Each new bundle multiplies this tax**, and the tax is
worst exactly where the new abstraction is supposed to pay:

```math
theorem MetricSpace.IsCompact.image (source target : MetricSpace)
        (f : MetricSpace.carrier(source) → MetricSpace.carrier(target))
        (region : Set(MetricSpace.carrier(source)))
        (compact : MetricSpace.IsCompact(region))
        (continuous : MetricSpace.ContinuousOn(f, region))
        : MetricSpace.IsCompact(MetricSpace.imageSet(f, region))
```

A mathematician writes *"let X, Y be metric spaces, f : X → Y, A ⊆ X."* With a
carrier coercion this is `(f : source → target)` and `(region : Set(source))`.
`Metric/topology.math` is otherwise a genuinely good file; the projections are
the only thing standing between it and reading like a textbook.

### What to build

A coercion registry exists (`src/elaborator/coercion.cpp`) and handles numeral
lifting, the ℕ→ℤ→ℚ→ℝ embeddings, and quotient bridges.
`docs/conventions/structures-and-inference.md` says instance resolution
"mirrors the coercion registry". Two cases are missing:

- **structure-as-its-carrier** — `(a b : r)` elaborates to
  `(a b : Ring.carrier(r))` when `r : Ring`, and likewise
  `(f : source → target)` for `source target : MetricSpace`
- **subtype-to-base** — a `NaturalsBelow(n)` where `ℕ` is expected inserts
  `.value`; a `ℕ` with `i < n` in context inserts `.make`

The registry's existing "at most one instance per `(structure, carrier)`" rule
is the coherence condition, already stated and enforced. `8a898f6a` already
taught `instance` to read a bundle's carrier off its constructor telescope
rather than a name table — that is the piece a general carrier coercion needs.

**Acceptance:** carrier and `.value` occurrences inside proof bodies drop by an
order of magnitude with no proof text hand-rewritten beyond deleting
projections; `MetricSpace.IsCompact.image` reads as above.

### 1a DONE — structure-as-its-carrier (`5255fe09`, `514028e4`)

`MetricSpace.carrier` across `library/`: **506 → 0** (the 8 that remain are
inside `Test/bundle_carrier_coercion_test`, where writing the projection
explicitly is the point). `MetricSpace.IsCompact.image` reads as the target
above, verbatim, and no proof text was rewritten — only projections deleted.

A bundle is recognised exactly as `instance` recognises one (`8a898f6a`) — by
a `<Structure>.carrier` projection being in scope — so there is no name table
and `Ring` / `Field` / `VectorSpace` / any future bundle qualify on the same
terms. Two guards: the term's type must not already be a Sort (genuine types
untouched), and in argument position the *expected* type must be a Sort
(without which `source` inside `MetricSpace.carrier(source)` would itself be
wrapped).

**Measured effect: horizontal, not vertical.** `Metric/` is 3,670 lines before
and after. Nothing got shorter by a line; every signature got shorter by a
*concept*. Judge the change on the diff, not on a line count:

```math
-- before
(f : MetricSpace.carrier(source) → MetricSpace.carrier(target))
(region : Set(MetricSpace.carrier(source)))
-- after
(f : source → target)
(region : Set(source))
```

Three things for whoever does 1b/1c:

- **Wire every binder path, and check `make tests`, not just a verify.** The
  two-stage build has two of them — `elaborateDefinition` and
  `elaborateTheoremStatementOnly` (stage 1, `MATH_STATEMENTS_ONLY=1`). Wiring
  only the first left stage 1 building a Pi over a non-Sort domain, which
  surfaces as `internal: expected a Sort when computing universe level` at
  1:1. A direct `kernel verify` passes; only the interface stage fails.
- **Universe-polymorphic heads infer their level before argument coercion
  runs.** `∃ (x : m). …` desugars to `Exists(m, …)`; the level comes from the
  arguments, so the bundle has to be unwrapped at the *probe* stage
  (`domainAtIsSort` gates it) or the call fails with "could not infer 1
  universe level of 'Exists'". Any `.value`/`.make` coercion in 1b/1c will hit
  the same thing.
- **`.make` (ℕ → `NaturalsBelow(n)`) is a different mechanism and should be
  costed separately** — it is proof-carrying (`i < n` discharged from context),
  which neither of the above is.

### 1b — mechanism DONE (`407587ea`, `ea529776`, `63eba046`); the sweep is NOT mechanical

`coercion (NaturalsBelow, Natural) := NaturalsBelow.value` is registered and
works: `s(i)`, `i = v`, `i + 0`, `i < n`, `i + j`, and a calc endpoint absorbed
into an ℕ carrier. Three elaborator changes were needed —

- a coercion function may now carry **leading implicit** parameters (every
  subtype projection has this shape; the registry checked the first Pi domain
  and so could express none of them). The kernel has no implicits, so the
  application solves them from the source type — which must be **closed** over
  the local binders first, or you get "unbound internal variable";
- a **homogeneous unregistered operand pair** (`i + j`) now coerces both sides
  to the nearest type carrying the operator. It runs **after** the
  expected-type fallback, deliberately: first, it made `1 / k!` at an ambient
  ℝ dispatch as *integer* division;
- calc endpoints thread their type through, for a chain that changes carrier.

**But the sweep is a per-site judgment call, unlike 1a — do not batch it.**
`Set/finite.math` deliberately gives `NaturalsBelow` *its own* relational
vocabulary (`NaturalsBelow.LessThan` / `LessOrEqual`, registered on `<` / `≤`).
So deleting `.value` between two indices does not delete a projection, it
**changes which proposition is stated**:

```math
-- ℕ-order on the values; `Natural.lt_or_gt_of_ne` cites it
NaturalsBelow.value(a) < NaturalsBelow.value(b) ∨ NaturalsBelow.value(b) < NaturalsBelow.value(a)
-- the INDEX order — one δ-step away, and the citation no longer matches
a < b ∨ b < a
```

Worse for equality: `a ≠ b` at `NaturalsBelow` is not `value(a) ≠ value(b)` —
they are bridged by `equal_of_value` plus proof irrelevance, not by δ. A blind
sweep of `Permutation.sign_swap` turned its opening `value(a) ≠ value(b)` into
a restatement of its own hypothesis and broke the proof.

**The rule the sweep must follow:** delete `.value` only where the context
*forces* a ℕ — an argument to an ℕ-function, mixed arithmetic, a comparison
against a bound like `i < n`. Leave it wherever both sides are indices, where
the index-level spelling is the better one anyway and citations are resolved
against it. That is judgment per site, not `replace_all`.

Measured shape of the work: **662** sites are a bare identifier
(`NaturalsBelow.value(i)`, 15 distinct spellings), **407** are compound
(`NaturalsBelow.value(sel(i))`, 108 distinct spellings), over 21 files. The
bare-identifier ones are where the index-vs-value hazard concentrates, so
"bare = easy" is exactly backwards.

`Set/finite_sum.math` is swept as the worked example (37 sites, all genuinely
ℕ-forced).

---

## 2. `VectorSpace.linearCombination` should be indexed by a list

Unchanged since `bea1113`. `Algebra/` contains **two incompatible finite-sum
idioms** and the worse one carries the linear algebra.

The good one, `Algebra/matrix.math` (449 uses):

```math
CommutativeRing.sumOver((k : NaturalsBelow(middle)) ↦ left(i, k) * right(k, j),
    NaturalsBelow.enumerate(middle))
```

Its file header says why: *"no clamp of a plain `Natural` back into the index
type, and the empty range (middle = 0) is the empty list."*

The bad one, `Algebra/linear_combination.math` + `Algebra/span.math` (342
uses) — a combination is a count, an *injective selection function* `ℕ → I`,
and coefficients `ℕ → F`:

```math
definition VectorSpace.LinearlyIndependent (family : I → carrier(V)) : Proposition :=
  ∀ (count : ℕ). ∀ (selection : ℕ → I). ∀ (coefficients : ℕ → carrier(f)).
      (∀ (i j : ℕ). i < count → j < count → selection(i) = selection(j) → i = j)
      → linearCombination(family, coefficients, selection, count) = zero(V)
      → ∀ (i : ℕ). i < count → coefficients(i) = zero(f)
```

`NaturalsBelow.clamp` appears in exactly two files —
`Algebra/rank_nullity.math` (2,185 lines) and `Algebra/exchange_lemma.math`
(1,036) — and those are precisely the files using this idiom. The selection
cone (`rank_nullity`, `exchange_lemma`, `basis_pruning`, `span`,
`linear_combination`) is 4,834 lines for a standard first course.

The tell, in `LinearMap.appended_images_independent`. Reindexing needs a
**total** `ℕ → NaturalsBelow(sz)`, which needs a fallback, which needs `target`
already introduced:

```math
let selExtFallback : NaturalsBelow(sz) :=
    NaturalsBelow.make(k + NaturalsBelow.value(sel(target)), selExtBound(target, targetBelow));
let selExt : ℕ → NaturalsBelow(sz) :=
    (i : ℕ) ↦ NaturalsBelow.clamp(selExtFallback)(k + NaturalsBelow.value(sel(i)));
```

The proof's binder order is dictated by a totality workaround.

**Do:** restate `linearCombination` as `sumOver(family, indices)` over a list,
with `Lists.NoDuplicates(indices)` replacing the injective-selection side
condition. Reindexing becomes `map`. `NaturalsBelow.clamp` should be deletable.

**Read the provenance note below before starting** — this reopens a recorded
decision, and the reasons it was decided are worth engaging with rather than
overriding.

**Sequencing:** independent of item 1, but item 1 shortens the rewritten proofs
considerably. Do 1 first if both are planned.

---

## 3. `for … sufficiently near …` — the filter scope

**Layer B of this item landed** (the metric bundle). What remains is Layer A,
which the bundle made strictly cheaper: `Near` is now **one** registry entry
over `MetricSpace`, resolved by instance search, instead of one per carrier.

### What exists

`elaborateEventuallyScope` (`src/elaborator/induction.cpp`) depends on exactly
**five hardcoded strings**: `Natural.Eventually`, its `.of_always`, `.and`,
`.monotone`, and the binder domain type `"Natural"`. The fold, the δ-reduced
recogniser (`recognizeUnfoldedEventually`), the β-redex peeling for facts from
`choose`, and the binder handling are already generic.

### The unifying observation

`max`, `min`, and `∩` are the same operation: the filter's `and`.

| filter | directed by | combine with |
|---|---|---|
| `eventually` (ℕ) | `≥` on thresholds | `max` |
| `near x` (metric) | `δ` | `min` |
| `near x` (topological) | `⊇` on neighbourhoods | `∩` |

The elaborator never looks inside — it cites the registered `.and` and folds.

### Proposed syntax

One family, statement/scope distinguished by `.` versus `:`, which is what
`eventually` already does:

```math
for <binder> <filter phrase>. <proposition>        -- statement position
for <binder> <filter phrase>: { <proof> }          -- goal position
```

```math
for m sufficiently large. abs(s(m) - limit) < ε
for y sufficiently near x. MetricSpace.distance(f(x), f(y)) < ε
for y sufficiently near x in region. …
```

**Binder first** (`for y sufficiently near x`, not the current
`for sufficiently large m`) so the bound name sits where a reader looks for it
and the phrase reads as English in both positions. **Parameters live in the
phrase**, which is what lets `near` take a point and `near … in …` take a
carrier while `large` takes nothing.

### The registry

Mirror the instance and coercion registries: phrase with parameter slots,
predicate constant, binder domain type, and the `of_always` / `and` /
`monotone` lemma names. `max` versus `min` lives entirely in the registered
`.and`; no filter-specific code in the elaborator.

Resolution keyed on `(phrase, domain type)`, taken from the filter's parameter
where there is one — with the bundle, `near x` resolves through
`{m : MetricSpace}` from the type of `x`, so ℝ and the plane share one entry.
Allow `for (m : ℝ) sufficiently large.` where ℕ and ℝ both want
`sufficiently large` (limits at infinity).

### Current cost of not having it

```
Real/derivative.math        min: 45
Real/continuity.math        min: 20
Metric/topology.math        min:  6
Metric/continuity.math      min:  6
Real/limits.math            Natural.maximum: 25 → 0   (done, 3ac96946)
Metric/separation.math      Natural.maximum:  5
Metric/uniform.math         Natural.maximum:  2
```

Note the last two: the newly written generic files brought **new** max
bookkeeping. This is not a legacy problem being cleaned up, it is an ongoing
tax on new work.

### Retire `eventually`?

Recommend yes — it is the only filter with its own keyword, it hardcodes ℕ, and
the prose spelling already exists, so two vocabularies are maintained for one
filter today. 32 sites. If kept, keep it as a registered *alias*, not a
parallel code path.

### Three places it does not generalise cleanly

1. **`Natural.Frequently` is not a filter.** `∀N ∃m > N` is not `and`-closed.
   `for arbitrarily large m. P(m)` is fine as a statement binder; the scope
   form is meaningless — nothing to fold. Register the binder, refuse the
   scope, make the error say why.
2. **Punctured vs unpunctured `near`.** `HasDerivativeAt` and `ContinuousAt`
   are unpunctured; a limit of a function at a point needs the punctured
   filter. Different `and` lemmas. **Decide before writing `Near`** —
   retrofitting splits every downstream statement. The `limits.math` rewrite
   sharpened this: the decision is not only about `and`, it is about
   **properness**, which the punctured filter has only at a non-isolated
   point — automatic in ℝ and the plane, false in a general `MetricSpace`.
   Since properness is what every contradiction argument closes on (finding 1
   above), a punctured `near` registered over the bare bundle would be
   unusable exactly where it is most wanted.
3. **One-sided.** `sufficiently near x from above` will be wanted for one-sided
   derivatives. Nothing to build now; just keep `near` parameterizable.

### Two prerequisites, both cheap

- **Document the scope form.** `eventually (m): { … }` and its prose spelling
  `for sufficiently large m: { … }` are implemented, tested
  (`library/Test/eventually_test.math`), and appear **nowhere in `docs/`**:
  `grep -rn "sufficiently large\|eventually (" docs/` returns nothing.
  `docs/reference.md` documents `take`, `witness`, `choose`, and the bounded
  range check but not this. Two library files use it. C4 of
  `PLAN_LANGUAGE_IMPROVEMENT.md` already requires docs in the same commit as
  the construct; this one slipped. **Still outstanding** — and now it also
  owes the three new `Natural.Eventually` lemmas below.
- ~~**Rewrite `Real/limits.math` with it.**~~ **DONE (`3ac96946`).** Findings
  below; they are the reason this was the first move.

### What the `Real/limits.math` rewrite turned up

`Natural.maximum` 25 → 0 (the import went too), 539 → 510 lines, every
theorem in the file converted. The scope carries more than advertised:
`Real.SequenceConverges` is *already* defined as `eventually (m). …`, so the
file had been discharging a filter-shaped goal by hand all along. In
`SequenceConverges.add` the conversion removed not just the `maximum` and the
two `≤ m` projections but the two per-fact instantiation lines as well — the
scope supplies each eventual hypothesis at the bound index for free.

Five things the design needs to absorb **before** `Near` is written:

1. **Three filter lemmas were missing, and each has a `Near` analogue.** The
   registry's `of_always` / `and` / `monotone` triple is not sufficient:
   - **properness** (`Eventually.holds_somewhere` : what holds eventually
     holds somewhere) — the elimination form. **This is the sharpest new
     constraint on open question 2 below.** Properness is what lets a limit
     argument by contradiction close. The *punctured* `near x` is proper only
     when `x` is not isolated — which is automatic in ℝ and the plane but
     **false in a general `MetricSpace`**. So the punctured filter cannot be
     registered over the bundle unconditionally; it needs a non-isolated-point
     side condition, or it must be registered only for the spaces that have
     one. Decide this with the punctured/unpunctured question, not after.
   - **`Eventually.not_eventually_false`** — the shape a contradiction
     argument actually ends on. `le_of_eventually_le` / `ge_of_eventually_ge`
     each spelled `Natural.maximum(N, M)` eight times to say exactly this.
   - **`Eventually.shift`** (translation invariance). See 2.
2. **The scope instantiates every fact at the bound variable and nothing
   else.** `SequenceConverges.shift_one` needs its hypothesis at `1 + m`, and
   is therefore *outside* the scope — it is the one theorem in the file the
   construct could not do, and it needed `Eventually.shift` instead. The
   `Near` analogue is pushforward along a map, and it will be wanted far more
   often than the ℕ case (any argument that reasons at `f(y)`, at a midpoint,
   or at a second point). **Register a shift/pushforward lemma beside `.and`
   from the start.**
3. **There is no explicit-threshold introduction form.** In
   `monotone_bounded_converges` the threshold comes from an existential, not
   from another filter, and the only way in is a raw `by witness N with …`.
   The missing form is `for m past N: { … }` (and, for `Near`,
   `for y within δ of x: { … }`). Both filters need it; it is the intro that
   pairs with properness as the elim.
4. **Higher-order argument inference does not survive a transformed index.**
   `Eventually.shift`'s conclusion is `Eventually((m) ↦ P(offset + m))`.
   Neither `P` nor `offset` can be inferred from the goal — the citation
   needs *both* named, which is precisely the spelled-out argument list
   `docs/style.md` exists to remove:
   ```math
   by Natural.Eventually.shift(P := (m : ℕ) ↦ abs(s(m) - limit) < ε, offset := 1)
   ```
   The matcher does not β-normalise after instantiating a predicate variable,
   so `P(offset + m)` never matches a concrete body. **Any registry lemma
   stated with the predicate applied to a transformed point hits this.**
   Either keep every registered lemma's predicate applied to the bound
   variable alone, or fix the matcher — the second is the real fix and is
   worth scoping before the registry multiplies the lemma count.
5. **An elaborator bug on the scope's own error path — found and fixed.**
   `elaborateBlockTail` keeps a `tailIsProofOnly` list of tail forms whose
   direct-reading failure must be rethrown rather than fall through to the
   stated-proposition reading (which re-elaborates with no expected type).
   `SurfaceEventuallyScope` was missing from it, so *any* failing scope body
   under a δ-reducing goal reported `` `eventually (m): …` needs an expected
   type from context `` — pointing at the goal, which was fine, instead of at
   the claim that did not close. Fixed in `3ac96946`; pinned by
   `library/ErrorTest/eventually_scope_body_failure`.

**Follow-up this exposed, not done here.** Two signatures spell the filter by
hand instead of taking one: `Real.SequenceConverges.of_rational`'s
`rationalBound` parameter (`∃N. ∀m ≥ N. …`), and
`le_of_eventually_le` / `ge_of_eventually_ge`, which take `(N : ℕ)` plus
`(tail : ∀ m. N ≤ m → …)` — the latter pair being *named* for an eventuality
they do not accept. Taking `eventually (m). …` drops a parameter from each.
16 call sites across 7 files (`Metric/interval`, `Plane/model`,
`Real/exponential`, `Real/exponential_addition`, `ComplexNumber/*`), so it is
its own scoped pass.

---

## 4. `Real/` never joined the metric layer

**New item.** The port unified `Plane/` with the generic layer and left the
analysis layer as an island.

```sh
grep -l "^import Metric" library/Real/*.math | wc -l      # → 0
```

`Real/continuity.math:40` still carries a carrier-free definition:

```math
definition Real.ContinuousAt (f : ℝ → ℝ) (x : ℝ) : Proposition :=
  ∀ (ε : ℝ). ε > 0 → ∃ (δ : ℝ). δ > 0 ∧ ∀ (y : ℝ). abs(y - x) < δ → abs(f(y) - f(x)) < ε
```

while `MetricSpace.ContinuousAt` says the same thing relative to a carrier, and
`Real.metricSpace` (`Metric/real.math`) is a registered instance. So the ε-δ
text now exists twice, and the copy that is *not* connected sits in the layer
with the most ε-δ proofs. There is no bridge lemma in either direction.

**Do:** make `Real.ContinuousAt` / `ContinuousOn` the `Set.universe` (or
interval) case of the generic notion, with `Real/derivative.math` and
`Real/intermediate_value.math` following. This is the same deduplication the
metric port performed for `Plane.RealContinuousAt`, which is now a two-line
alias in `Plane/extremum.math`.

**Sequencing:** do this before item 3. Otherwise `Near` gets registered against
a `Real.ContinuousAt` that is about to be redefined, and `Real/derivative.math`
— the largest single beneficiary of item 3 — converts twice.

### DONE — re-layered, then redefined (`ae7f0a23`, `fa5ba885`)

`Real.ContinuousAt` **is** the generic notion now, as this item asked:

```math
definition Real.ContinuousAt (f : ℝ → ℝ) (x : ℝ) : Proposition :=
  MetricSpace.ContinuousAt(f, Set.universe(ℝ), x)
```

The re-layering that unblocked it cost **two import lines**. The four
bridge lemmas of `7aa45c4a` are retired;
`MetricSpace.ContinuousAt.restrict` stays (a real gap in that API).

Three things worth keeping:

- **The seal was the whole obstacle, and it was cheap to move.** Lifting
  `square_root → intermediate_value → continuity → derivative` out of
  `Real/cauchy.math` and `Real/interface.math` broke exactly two files
  (`Real/arithmetic_geometric_mean.math`, `ComplexNumber/modulus.math`,
  both reaching `Real.square_root` through the interface) plus the test
  that asserted continuity survives the seal. Continuity is topology; it
  was never part of the number system's interface.
- **The two spellings are not defeq, and no re-layering fixes that.**
  `distance(x, y)` is `abs(x - y)` where analysis writes `abs(y - x)`, and
  the universe carrier leaves a vacuous `y ∈ universe` premise that no
  reduction removes. So the boundary is a characterising pair
  (`conventions/opaque.md`) — but it is drawn **once**, and
  `derivative.math` / `intermediate_value.math` mention `distance`
  **zero** times.
- **The elimination form is what made it cheap.**
  `Real.ContinuousAt.tolerance` takes ε directly, so callers write
  `choose δ such that … from Real.ContinuousAt.tolerance` with both
  premises discharged from context. That replaced direct positional calls
  (`from fContinuous(ε / 2, halfPositive)`), so the nine converted call
  sites got *shorter*. A characterisation that takes the whole `∀ε.∃δ.…`
  instead would have forced a restatement at every use — worth remembering
  when item 3 designs `Near`'s registry lemmas.

### Superseded: the first attempt bridged instead (`7aa45c4a`)

**Why the redefinition is not available *as the tree is laid out today*.**
`Metric/space.math` imports `Real.interface`, and `Real/interface.math` — the
seal (`interface module Real.interface implemented by Real.cauchy`) — imports
the entire Real subtree, topology included: `Real.intermediate_value` (61),
`Real.square_root` (70), `Real.continuity` (71), `Real.derivative` (72).
`Real/cauchy.math`, the construction the seal is implemented by, imports the
same four at its lines 43–46. So every `Metric.*` module sits above *all* of
`Real/`, and `Real/continuity.math` importing `Metric.continuity` is a cycle.

**But nothing requires that, and the fix is small in principle.** What pins
the topology below the seal is a single chain — `√` is part of the public
view (`constant Real.square_root` in the interface), `√` is constructed from
the intermediate value theorem, and IVT needs continuity. It is a real
mathematical dependency, but it is a dependency of *constructing √*, not of
anything the metric layer needs. Measured:

```sh
grep -rho "square_root" library/Metric/*.math | wc -l      # → 0
```

Every consumer of `Real.square_root` — `Plane/norm.math`, `ComplexNumber/*`,
`GaussianInteger/fermat_two_squares.math`,
`IntegerMod/square_root_of_minus_one.math` — is **above** the metric layer.
So the chain `square_root → intermediate_value → continuity → derivative` can
be lifted out of the seal and placed above `Metric/`, after which
`Real.ContinuousAt` can be *defined* as
`MetricSpace.ContinuousAt(f, Set.universe(ℝ), x)` and this item's original
"Do" goes through as written.

That re-layering is its own step, not a side effect of a bridge: it drops four
imports from `Real/cauchy.math` and from `Real/interface.math`, removes
`Real.ContinuousAt` / `ContinuousOn` / `HasDerivativeAt` from
`export definitions` and the `constant Real.square_root` declaration from the
public view, and updates whatever reached those through
`import Real.interface` alone (`library/Test/real_interface_consumer.math`
tests exactly that exposure). It touches the sealed-structure mechanism of
`PLAN_LANGUAGE_IMPROVEMENT.md` D3/D3a, so it wants its own pass.

What landed instead is the bridge, following the
`Real.metric_SequenceConverges` / `Real.SequenceConverges.of_metric` pair that
was already in `Metric/real.math`:

```
Real.metric_ContinuousAt            Real → metric, at Set.universe
Real.ContinuousAt.of_metric         metric → Real
Real.metric_ContinuousOn            pointwise on a region
Real.metric_ContinuousOn_interval   from the (a, b) endpoint form
MetricSpace.ContinuousAt.restrict   (gap: the ContinuousOn version existed)
```

Three things worth carrying forward:

- **The duplication is now connected, not removed.** The ε-δ text still exists
  twice. That was the stated defect ("no bridge lemma in either direction") and
  it is fixed, but anyone expecting a line-count win should not.
- **`Real.ContinuousOn` is not the metric `ContinuousOn`.** `Real.ContinuousOn(f, a, b)`
  is *ambient* continuity at each point of [a, b]; `MetricSpace.ContinuousOn(f, S)`
  restricts both quantifiers to `S`. The first is strictly stronger — a function
  can be continuous relative to [a, b] and discontinuous at `a` ambiently. So
  that bridge is one-directional **by mathematics**, and this item's parenthetical
  "(or interval)" hid a real distinction. Any future attempt to unify the two
  notions changes what `intermediate_value` and `derivative` assume.
- **`Real/derivative.math` and `Real/intermediate_value.math` did not need to
  change**, which is the upside of bridging: item 3 can now register `Near`
  against a `Real.ContinuousAt` that is *not* about to be redefined, so the
  "converts twice" risk this item was sequenced to avoid is gone either way.
  If the re-layering above is taken first, they convert once, properly.

---

## 5. Bounded quantifiers in statements

`take x > 0;` exists on the proof side (`docs/reference.md`, "Combined ordered
binder"). There is still no `∀ ε > 0.` or `∃ δ > 0.` for statements:

```sh
grep -ohP "∀ *[a-zA-Zε] *> *0\." library/*/*.math | wc -l     # → 0
```

Two costs. First, every ε-δ definition is longhand. Second — and this is the
important one — the `∃ (δ : ℝ). δ > 0 ∧ P(δ)` shape is the **upstream cause**
of the conjunct-projection noise fixed in `Plane/` by `1cc9b73`. In
`Real.HasDerivativeAt.multiply`, each of four `choose`s is followed by a hand
restatement of the second leg:

```math
choose fδ from fDerivative(ε / 2 / gHeadroom, fTolerancePositive);
∀ (y : ℝ). abs(y - x) < fδ
        → abs(f(y) - f(x) - fSlope * (y - x)) ≤ ε / 2 / gHeadroom * abs(y - x) as fClose;
```

A bounded `∃ δ > 0. P(δ)` whose `choose` drops `δ > 0` and `P(δ)` into context
as **separate** facts removes all of these.

The interval migration added a second motivation. Statements now read:

```math
(s t : ℝ) (sInside : s ∈ Real.unitInterval) (tInside : t ∈ Real.unitInterval)
(sBeforeFinish : s ≠ 1) (tBeforeFinish : t ≠ 1) (ordered : s < t)
```

That is a large improvement on what it replaced, but it is still six
hypotheses where a mathematician writes `0 ≤ s < t < 1`. A bounded binder over
an interval would close the remaining gap.

**Do this after item 3**, which changes what these definitions look like.

---

## 6. `let` is not being used in `Real/`

`docs/style.md` names `let` as "the main lever for *un-chopping* a proof that
has sprawled across many narrow lines". `Real/` does not use it.
`Real.HasDerivativeAt.multiply` spells out `min(min(fδ, gδ), min(nearδ,
differenceδ))` six-plus times and peels it with a cascade of
`Real.minimum_LessOrEqual_left` / `_right`. `Plane/connected.math` shows
`let room : ℝ := min(…)` works fine, so nothing blocks it.

**Caveat:** item 3 deletes most of these `min`s outright. If item 3 is
happening, skip this for `derivative.math` and `continuity.math` and apply it
only where the `let` is not about δ-juggling.

---

## Provenance — checked against all 32 `PLAN_*.md` (14,737 lines) and `docs/`

| Item | Status in existing plans |
| --- | --- |
| 1 carrier / subtype coercions | **New.** |
| 2 list-indexed `linearCombination` | **Decided against — a different alternative was evaluated.** |
| 3 filter scope / `near` | **New.** Layer B (metric bundle) has since been built as `PLAN_METRIC_TOPOLOGY.md`; Layer A is still unplanned. |
| 4 `Real/` island | **New.** |
| 5 `∀ ε > 0.` | **Already known, logged as not-built.** |
| 6 `let` in `Real/` | Not a plan item; `docs/style.md` already prescribes it. |

**Item 1.** `PLAN_COERCIONS.md` is entirely the concrete number tower
(`ℕ ↪ ℤ ↪ ℚ ↪ ℝ ↪ ℂ`) for mixed-type arithmetic; it explicitly scopes out
non-injective casts and parameterized types, and never uses the words
"carrier" or "subtype". The nearest relative is in `PLAN_READABILITY.md`
(~lines 245–295): operator *dispatch* over carrier projections, i.e. making
`+`/`*` resolve on a value typed `Ring.carrier(r)`. That solves "operators
resolve"; it does not remove the spellings.

**Item 2.** `docs/PLAN_GENERIC_AGGREGATION.md`, "Index bridge for finite
families" (PLAN_LINEAR_ALGEBRA Stage 0.4, decided 2026-07-12):

> Rejected alternative: extending a `NaturalsBelow(k) → A` family to
> `Natural → A` with a default — needs a proof-carrying conditional per use
> and either a second fold or a bridge lemma family; the function+bound form
> needs zero new machinery and is how the analysis layer (`Real.partialSum`)
> already speaks.

Sound on its own terms, but **not** the list-of-indices form.
`sumOver(f, NaturalsBelow.enumerate(n))` needs no default and no conditional.
Two points for whoever revisits it:

- The consistency argument cuts both ways. `Real.partialSum` speaks
  function+bound; `Algebra/matrix.math` speaks list-of-indices. The library
  already has both.
- **The rejected mechanism came back anyway.** `NaturalsBelow.clamp(fallback)`
  *is* extending a family with a default — now done by hand inside proofs (40
  sites) rather than once in the library, with the fallback's construction
  dictating binder order.

**Item 3.** The closest prior remark is a parenthetical in A6
(`PLAN_LANGUAGE_IMPROVEMENT.md:2152`): *"or a new `Logic/eventually.math`
generic over an ordered index"*. Not taken — it shipped as
`Natural/eventually.math`, hardcoded to ℕ — and narrower anyway: A6's
motivation names Real, PAdic and ComplexNumber *sequences*, all directed by `≥`
on an index, and it states outright *"a lightweight, hardcoded fragment of
filters; the general theory is not needed."* Item 3 revisits that call on
evidence A6 did not have.

**Item 5.** `PLAN_LANGUAGE_IMPROVEMENT.md:3415` uses `∀ ε > 0.` in the
reference target; line ~1214 records it as a textual delta — *"combined-header
sugar NOT built yet"*. The `take ε > 0;` half **has** since been built. Treat
item 5 as finishing a logged delta.

---

## Not worth doing

**Variadic `min`.** Considered and rejected. Nullary `min` needs a top element
ℝ has not got, and item 3 removes the `min`s rather than shortening them.

**Import reduction.** 10,604 import lines across ~120,000 (8.8%); worst files
carry 67. Non-transitive imports are a defensible explicitness choice and this
does not affect how proofs read. Noted only so it is not rediscovered.

---

## Bookkeeping

`scripts/clean_manifest.txt` contains **zero** entries from `library/Plane/`
(7,606 lines) and **zero** from `library/Metric/` (3,638 lines) — the latter
written entirely in the last two days. Compare the linear-algebra work, whose
ledger records "manifest-added leak-free" at each stage. The topology and
geometry layers are not following the same discipline, and the manifest is
doing no work for roughly 11,000 lines of the library.

`Metric/topology.math`, `Metric/space.math`, `Plane/curve.math`,
`Plane/point.math`, and `Plane/segment.math` would all pass a read today.

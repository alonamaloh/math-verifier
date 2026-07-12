# PLAN: Remove the surface `cases` construct entirely

## North-star

Hide the CIC recursor completely behind math-like surface constructs. The
kernel eliminator is a primitive and stays; the ELABORATOR's dependent-motive
machinery stays (the desugarings need it). What goes is the **surface `cases`
keyword** — once nothing invokes it directly, delete it from the parser, and the
"it desugars to a recursor" fact becomes invisible, exactly as we already did
for the computed-scrutinee form.

Two things are already true (done in the prior session — see Status):
- `cases <computed expression>` is **rejected** by the elaborator.
- So every surviving `cases` in the library has a **variable** scrutinee.

This plan removes those too, then deletes the keyword.

## Status ledger (update every session)

- [x] **Computed-scrutinee `cases` rejected.** `elaborateCasesExpression`
  (src/elaborator/cases.cpp, ~line 1010) throws `ElaborateError` when
  `cases.userWritten && casesScrutineeIsComputed(scrutinee, localBinders)`.
  Message locked by `library/ErrorTest/cases_on_computed_expression.math`.
- [x] All pattern-cases ratchet/linter scaffolding deleted (Makefile targets,
  cic_leak_report category, `MATH_CHECK_PATTERN_CASES` env gate).
- [x] The 3 foundational/holdout sites migrated to argument-matching helpers:
  `Natural.compare_strict_shift`, `Natural.Raw.select_on_zero`,
  `Test.pick_on_zero` (in substituting_obtain_test).
- [x] **STEP 1 — Spike the residue.** Of the 98 multi-arm sites only 10 are
  value-level (9 `definition` + 1 `opaque`); the other 88 are proof-level
  (`theorem` ×80 + `automatic theorem` coverage lemmas ×8). Of the 10:
  3 `cases decision` lift to a pattern-match on the `Decidable` parameter;
  `floor_divide` reorders to a single-column match; `diagonalStep` is a
  nested single-param pattern (all verified against the kernel). The **only**
  hard residue is **5 double-split functions** (`monus`, `distance`,
  `maximum`, `Polynomial.Coefficients.add`, `Polynomial.nth`) that split two
  independent data args — no multi-column pattern rows (ErrorTest
  `pattern_shadows_constructor`), no helper (mutual recursion rejected).
  **BUT** all 5 admit single-column / non-recursive **reformulations** using
  existing primitives (monus/relu identity, value-level `if`, list head/tail,
  single-recursion) — so the genuine residue needing a NEW language feature is
  **0**. Recommendation adopted: reformulate rather than build multi-column
  matching or a value-level data-match keyword.
- [~] **STEP 2 — Migrate 129 single-constructor destructures** → `let ⟨…⟩ :=`.
- [~] **STEP 3 — Migrate 98 multi-constructor splits** → `by cases` /
  `by induction` / `choose` / helper / **reformulation** (for the 5 residue).
  Done so far (reformulations, full library + tests green, downstream untouched):
  - `Natural.maximum := a + monus(b, a)` — non-recursive; inequalities re-prove
    from monus lemmas (left = less_or_equal_add_right; right = totality split).
  - `Natural.distance := monus(a,b) + monus(b,a)` — char lemmas
    (zero_left/_right/_succ_succ + 1+ form) recover the recursion; metric
    proofs re-derive through them; `add_left_cancel`/`respects` collapse via new
    `Natural.monus_add_common_left`/`_right` (added to monus.math).
  Remaining residue reformulations: `Natural.monus` (single-recursion on 2nd
  arg via predecessor), `Polynomial.nth` (value-level `if index = 0`),
  `Polynomial.Coefficients.add` (single-recursion + head/tail helpers). Plus the
  5 clean value-level lifts and the 88 proof-level migrations.
- [ ] **STEP 4 — Remove the `cases` keyword** from parser + elaborator surface;
  keep the recursor engine for desugarings. Add an ErrorTest that a bare
  `cases` keyword is now unknown syntax.

## The data (measured 2026-07-12, library proper, excludes Test/ErrorTest)

**227 `cases <variable>` sites**, split by arm count:

| Bucket | Count | Replacement |
|---|---|---|
| single-constructor (1 arm) | **129** | `let ⟨a, b⟩ := r` destructuring-let, or a projection |
| multi-constructor (2+ arms) | **98** | `by cases` / `by induction` / `choose` / helper |

Family breakdown (by first-arm constructor; approximate):
- Multi-constructor: `Natural` (zero/successor) ≈47, `Or` ≈15,
  `Logic.Decidable` ≈6, `Sum` ≈5, plus custom data.
- Single-constructor: `Ring` 7, `Group` 4, `Field`, `VectorSpace` 6,
  `Product` 11, `Subtype` 2, `List` 6, `Polynomial.Coefficients` 6,
  `RationalRepresentative`/`IntegerRepresentative`/`rep_*` (quotient reps) ≈30,
  `And` 2, tuple-pattern (`| ⟨a,b⟩`) destructures ≈24, …

Reproduce the counts:
```
python3 - <<'PY'
import os, re
root="library"
def bodies(text):
    for m in re.finditer(r'\bcases\s+([A-Za-z_][A-Za-z0-9_.]*)\s*\{', text):
        if m.group(1)=="by": continue
        i=m.end(); depth=1; arms=0
        while i<len(text) and depth>0:
            ch=text[i]
            if ch=='{':depth+=1
            elif ch=='}':depth-=1
            elif ch=='|' and depth==1:arms+=1
            i+=1
        yield m.group(1), arms
single=multi=0
for dp,_,fs in os.walk(root):
    if "/Test" in dp or "/ErrorTest" in dp: continue
    for fn in fs:
        if fn.endswith(".math"):
            for s,a in bodies(open(os.path.join(dp,fn)).read()):
                single += a<=1; multi += a>1
print("single:",single,"multi:",multi)
PY
```

## Migration recipes

### Single-constructor (STEP 2) — the mechanical bulk
`cases r { | Ctor(a, b, …) => body }` → `let ⟨a, b, …⟩ := r; body` (or, for a
single field, a projection). Structures (`Ring`, `Group`, `Field`,
`VectorSpace`, `Subtype`), quotient representatives, `And`, and existing
`| ⟨a,b⟩` tuple patterns are all this shape. Destructuring-let already exists
(parser desugars `let ⟨a,b⟩ := v in body` to a single-clause cases — see
`makeSurfaceCases` call in parser.cpp around line 2935, comment "Pattern-form
destructuring let"). NOTE: that desugaring itself emits a `SurfaceCases`
(userWritten=false) — fine, it's internal; it survives keyword removal because
it builds the node directly, not via the `cases` keyword.

### Multi-constructor (STEP 3)
- **Proof-level** (goal is a `Prop`): `by cases`. For a data VARIABLE the
  equation-shaped form works and discharges exhaustiveness against the
  auto-generated `<T>.cases_covered`:
  `by cases { case n = 0: … case n = successor(k) for some k: … }`.
  `Or` → `by cases { case A: … case B: … }`; `Exists` → `choose`/`obtain`;
  recursive `Natural`/`List` → `by induction`.
- **Value-level LOCAL data destructure** (inside a `definition` body returning
  DATA, casing a local data variable): this is THE RESIDUE. `if`/`by cases` are
  proof-level; the pattern-match-definition form only matches a *parameter*.
  Each such site becomes a named helper that pattern-matches its argument (the
  `select_on_zero`/`compare_strict_shift` move) — real indirection. STEP 1
  measures how many there are.

## STEP 1 — the spike (DO THIS FIRST, cheap, decides everything)

Count the multi-constructor sites that are **value-level local data
destructures** with no clean home. If small → just make helpers. If meaningful
→ decide whether to teach a value-level data-match / extend `by cases` to split
a data variable in value position BEFORE the bulk migration, so those stay
inline instead of proliferating helpers.

Heuristic to find them: a `cases <var> { | Ctor => }` whose enclosing construct
is a `definition` (not `theorem`) AND whose goal type is Type-valued (returns
data, not a proof). Grep for `cases` inside `definition …` blocks and inspect;
or instrument the elaborator (it knows the goal's universe at the cases site).

## STEP 4 — remove the keyword

- Parser: `parseCasesExpression` (src/syntax/parser.cpp ~3879) is the sole
  genuine-`cases`-keyword entry (dispatched from ~3692). Make the keyword a
  parse error pointing at the replacements. The desugarings do NOT go through
  it — they call `makeSurfaceCases(...)` / `elaborateCasesExpressionInner`
  directly, so they keep working.
- The `userWritten` flag on `SurfaceCases` (surface.hpp) then has only one
  consumer (the computed-scrutinee reject); once the keyword is gone there are
  no userWritten=true cases at all, so the reject + `casesScrutineeIsComputed`
  + `userWritten` can ALSO be deleted (nothing can reach them). Do this last.
- Keep: `elaborateCasesExpression`/`…Inner` engine, `by_representatives`,
  `by cases`, `by induction`, decide/if/choose/tuple-let desugarings.
- Add ErrorTest: bare `cases x { … }` now reports "unknown/removed syntax".

## Key code locations (verified this session)

- **Reject site**: src/elaborator/cases.cpp, top of `elaborateCasesExpression`
  (~1010). Throws for userWritten computed scrutinee.
- **`casesScrutineeIsComputed`**: src/elaborator/cases.cpp ~29 — SurfaceApplication,
  or a bare name whose innermost `LocalBinder` has a non-proof `value` that is an
  `Application`. Declared internal.hpp ~2907.
- **`userWritten` flag**: src/syntax/surface.hpp (SurfaceCases, ~289). Default
  false (synthetic); set true ONLY in `parseCasesExpression`. Two surface-tree
  rewrites must preserve it: `rewriteRecursiveCalls` (patterns.cpp ~1800) and
  `substituteSurfaceName` (parser.cpp ~301).
- **The engine**: `elaborateCasesExpressionInner` (cases.cpp ~1473) builds the
  dependent motive over the scrutinee. `elaborateDecideExpression` (cases.cpp
  ~934) shows `if`/decide reusing it ("replaced a bespoke ~270-line motive
  build") — this is WHY the engine can't be removed, only the surface keyword.
- **Desugarings that emit `SurfaceCases` (userWritten=false)**: parser.cpp
  makeSurfaceCases at ~301 (substituteSurfaceName), ~1288, ~2414/2448/2478,
  ~2935 (tuple-let); elaborator elaborateDecide/elaborateChoose/refining/with-eq.

## Verification workflow

- Build: `make -j 16 library` (warm rebuild sub-second; a `.cpp` change
  re-verifies the whole library). `make -j 16 tests` for Test/ feature files.
  `make check` for the full gate. `make error-tests` for the ErrorTest suite.
- ALWAYS `ulimit -v 12000000` before kernel/make runs (OOM guard).
- Per-file: `./kernel verify --source <f> --output /tmp/x.mathv --cache-root build`
  (add `--no-check-unused-names` for Test/ files).
- Owner rules (see MEMORY.md): edit .math with the Edit tool only (never
  sed/perl); commit often directly to main; proofs read like math (cite, don't
  call); readability is primary; `epsilon > 0` not `0 < epsilon`.

## Open design question (surface in the spike)

Do we want a value-level **data match** surface form (so multi-constructor
data splits inside definitions stay inline), or are helper functions
acceptable? `cases s { | Sum.left(x) => … | Sum.right(y) => … }` reads fine
today; forcing every such split into a named helper is the main readability
cost of full removal. The spike's count decides whether this question is worth
answering before STEP 3.

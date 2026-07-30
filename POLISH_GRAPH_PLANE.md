# Polish pass — `library/Graph/` and `library/Plane/`

Record of the readability sweep of 2026-07-29/30, and what is left. Prompted
by two external reviews of `Graph/` (both audited — see
`FRICTION_GRAPH_LAYER5.md` for the claims that did not hold up) and then
extended to `Plane/`.

**The build loops**: `make -j 16 graph` (14s, 52-module cone) and
`make -j 16 plane` (204-module cone). Full gate before committing:
`make -j 16 library`, `make -j 16 tests`, `make docs-check`.

**When checking a build, grep for `error` — not for the file you are
editing.** Grepping the filename hides a failure upstream of it, and `make`
stops there, so later files are never verified at all. That mistake cost three
theorems being reported as verified when they had not been compiled.

## Conventions this pass established

1. **Inclusion is `⊆`, on lists as on sets** — `List.Includes`
   (`Lists/list.math`), transparent, with `.reflexive`, `.transitive`,
   `.prepend`, `.prepend_both` and `.append_left` / `.append_right`
   (`Lists/append.math`). Never an inline `by { take …; suppose …; done }` for
   an inclusion.
2. **Name the object under construction with `let`.** Citations unify through
   a `let`-bound term, including in a `case` label and when the theorem's own
   conclusion spells the term out.
3. **`a ≠ b` and `a ∉ S`, never the `¬(…)` form.** One exception, forced:
   `suppose x ∉ S for contradiction` is not recognised as a reductio (friction
   L3 in `FRICTION_PLANE_LAYER6.md`), so that one position keeps `¬(x ∈ S)`.
4. **Introduce binders with `take` / `suppose`, never a restated-type lambda.**
   For a long body, open the block with `by {` on its own line and put the
   binders at the body's own indentation — the conversion then touches only the
   header instead of re-indenting fifteen lines.
5. **Lines may run to 140 columns**, and only wrap when they must.

## Done

**`Graph/`.** `⊆` swept (inline `by { take` 77 → 58, and what remains is
genuinely not inclusions — `pathgraph.math`'s ∀-forms run from a vertex LIST to
a `walkVertices` SET, or land on a disjunction). `let` bindings in `ear.math`,
`subdivision.math`, `pathgraph.math`, `three_leaves`, and the incidence proofs.
`Graph.other_vertex` replaced four copies. All 134 `¬(a = b)` and all `¬(a ∈ b)`
converted. All 11 numeral ascriptions dropped.

Measured and found to be pure noise — removing them changed nothing, so there
is no G6/G8-adjacent friction here: all 9 `(x := x)` named arguments and all 7
positional ∀-hypothesis citations.

**`Plane/` (including `Plane/Graph/`).** All ~40 restated-type lambdas
converted. `¬(a ∈ b)` swept. `pieces_meet_at_ends` binds the two cut points.
Both areas now peak at 107 columns with nothing over 120.

**Not changed, deliberately:** the `(0 : ℝ)` / `(1 : ℝ)` ascriptions in
`Plane/` are load-bearing, unlike the ℕ ones in `Graph/`. A bare numeral
defaults to ℕ, so `0 ∈ Real.unitInterval` elaborates as `Set Natural` and is
rejected. Tested; `polyline.math` was reverted after trying.

## Left undone, and why

1. **The redundancy pass on the OLDER `Plane/` files.** Census with
   `.mark_redundant.py`: `twoarcs` 93, `concatenate` 66, `component` 42,
   `extremum` 13 — 214 findings in four files. This is a per-site readability
   judgment where roughly **half are keeps** (`redundant_by_is_half_keeps`),
   so it is a substantial pass in its own right and doing it as a
   drive-to-zero would be worse than not doing it. The newer files
   (`segment_meet`, `Plane/Graph/*`) have been settled and are keeps-only.
2. **A general re-flow to 140 columns.** Both areas were written at ~90 and
   nothing now exceeds 120, so this is cosmetic rather than a rule violation.
   Worth knowing before attempting it: a blind join would make things worse,
   because much of the wrapping is deliberate — one clause per line in a
   multi-clause definition reads better than the joined line — and the owner's
   standing rule (`no_script_editing_of_math_files`) means it has to go
   through `Edit` site by site.
3. **`ear.math`'s duplicated `nearEnd`/`farEnd` arms** (the first review's
   item): hoisting one local fact before the split would remove ~24 lines of
   boilerplate. Not attempted.

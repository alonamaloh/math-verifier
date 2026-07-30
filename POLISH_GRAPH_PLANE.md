# Polish pass — `library/Graph/` and `library/Plane/`

Working checklist for the readability sweep begun 2026-07-29/30, so that a
fresh session can pick it up. Prompted by two external reviews of `Graph/`
(both audited — see `FRICTION_GRAPH_LAYER5.md` for the claims that did not
hold up) and then extended to `Plane/` at the owner's request.

**The build loops**: `make -j 16 graph` (14s, 52-module cone) and
`make -j 16 plane` (204-module cone). Full gate before committing:
`make -j 16 library`, `make -j 16 tests`, `make docs-check`.

**When checking a build, grep for `error` — not for the file you are
editing.** Grepping the filename hides a failure upstream of it and `make`
stops there, so later files are never verified at all. That mistake cost
three theorems being reported as verified when they had not been compiled.

## Conventions this pass established

1. **Inclusion is `⊆`, on lists as on sets** — `List.Includes`
   (`Lists/list.math`), transparent, with `.reflexive`, `.transitive`,
   `.prepend`, `.prepend_both` and `.append_left` / `.append_right`
   (`Lists/append.math`). Never an inline
   `by { take …; suppose …; done }` for an inclusion.
2. **Name the object under construction with `let`.** Citations unify through
   a `let`-bound term, including in a `case` label and when the theorem's own
   conclusion spells the term out.
3. **`a ≠ b`, never `¬(a = b)`.**
4. **Introduce binders with `take` / `suppose`, never a restated-type
   lambda** (`by (y : Plane.Point) (h : …) ↦ { … }`) — `docs/style.md` names
   this a raw-CIC tell.
5. **Lines may run to 140 columns.** Both areas were written at roughly 90 and
   read as chopped.

## `Graph/` — DONE

`⊆` swept (inline `by { take` 77 → 58, and what remains is genuinely not
inclusions: `pathgraph.math`'s ∀-forms run from a vertex LIST to a
`walkVertices` SET, or land on a disjunction). `let` bindings in `ear.math`
(`grown`/`pruned`), `subdivision.math` (`trimmed`/`subdivided`/`pruned`),
`pathgraph.math` (`pathPart`), `tree.math`'s `three_leaves`
(`excess`/`innerCount`), `basics.math`'s incidence proofs
(`firstEnd`/`secondEnd`). All 134 `¬(a = b)` → `≠`. All 11 numeral
ascriptions dropped. `Graph.other_vertex` replaced four copies.

Measured and found to be pure noise — removing them changed nothing:
- all 9 `(x := x)` named arguments;
- all 7 positional ∀-hypothesis citations.
So there is no G6/G8-adjacent friction here, contrary to what the review
suspected.

## `Plane/` — IN PROGRESS

Done: 15 restated-type lambdas converted to `take`/`suppose` across
`polyline`, `polygonal`, `segment`, `subarc`, `component`.

### Remaining, in value order

1. **~20 more restated-type lambdas.** Per file:
   `extremum.math` 5, `subarc.math` 5, `component.math` 3, `twoarcs.math` 3,
   `concatenate.math` 2, `polygonal.math` 1, `connected.math` 1. Mechanical:
   `by (x : T) (h : P) ↦ { body }` → `by { take x : T; suppose P [as h];
   body }`, re-indenting the body. Verify with `make -j 16 plane`.
2. **`⊆` and `let` audit.** `Plane/` already uses `⊆` idiomatically, but the
   `let`-for-a-repeated-term check has not been run on it. Look for repeated
   long terms the way `Graph/` was measured.
3. **Re-flow to 140 columns.** ~940 joinable continuation lines in `Graph/`
   alone were counted at 140; `Plane/` is similar. **This needs judgment, not
   a script**: much of the wrapping is deliberate (one clause per line in a
   multi-clause definition reads better than a joined line), so a blind join
   would make things worse. Also, the owner's standing rule
   (`no_script_editing_of_math_files`) forbids scripted `.math` edits, so this
   has to go through `Edit` site by site — which is why it is last.
4. **Redundancy pass** with `.mark_redundant.py` on both areas, judged per
   site (about half are keeps — see `redundant_by_is_half_keeps`).

### Do NOT change

The `(0 : ℝ)` / `(1 : ℝ)` ascriptions in `Plane/` are **load-bearing**,
unlike the ℕ ones in `Graph/`. A bare numeral defaults to ℕ, so
`0 ∈ Real.unitInterval` elaborates as `Set Natural` and is rejected. Tested
directly; `polyline.math` was reverted after trying.

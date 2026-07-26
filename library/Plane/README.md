# The plane

The Euclidean plane, built for the Jordan–Schönflies development
(`PLAN_JORDAN_SCHOENFLIES.md`). Two types, deliberately kept apart:

- **`Plane.Vector`** — a displacement. Carries the linear structure.
- **`Plane.Point`** — a location. Acted on by vectors, so `p + v` is a
  point and `q - p` is a vector.

Keeping them distinct is what makes `p + q` unwritable. The blueprint
already speaks this way — inversion is `a + (x - a)/‖x - a‖²` — and the
types should agree with it.

## Building

```sh
make -j 16 plane      # this area and exactly its transitive imports
```

Not `make library`: that verifies the Algebra/ fifteen-theorem material,
which dominates the wall clock. The `plane` target covers the 156-module
import cone — including 19 of the 546 Algebra files, the bundled-structure
basics that `Real`'s field and ring instances need — and nothing else.

About two seconds warm; about eighteen after a kernel or elaborator
change, which invalidates every module's proofs. The target asks for the
cone's proofs, not just its interfaces, so that second case is actually
re-verified rather than silently skipped (`scripts/module_cone.py`).

## Main definitions

- `Plane.Vector`, its coordinates `first` / `second`, `make`, `zero`, and
  the operators `+`, `-` (binary and unary), `*` for scaling by a real —
  [vector.math](vector.math)
- `Plane.Point`, `Plane.Point.position`, and the operators `+`
  (`Point + Vector → Point`) and `-` (`Point - Point → Vector`) —
  [point.math](point.math)
- `Plane.Vector.innerProduct`, `Plane.Vector.determinant`, and
  `Plane.Vector.perpendicular` — [bilinear.math](bilinear.math)
- `Plane.Vector.IsNonzero`, `Parallel`, `SameRay`, `OppositeRay`, and
  `Plane.Vector.Counterclockwise` — [direction.math](direction.math)
- `Plane.Vector.norm`, `Plane.Vector.supNorm`, `Plane.distance`, and
  `Plane.supDistance` — [norm.math](norm.math)

## Main theorems

- `Plane.Vector.equal_of_coordinates` and `Plane.Point.equal_of_position`
  — the bridges from coordinates to equations. **Every law goes through
  one of them**; reach for these rather than unfolding the construction.
- The coordinate-reduction lemmas `first_add`, `first_negate`,
  `first_scale`, `first_subtract`, `first_zero`, `first_perpendicular`
  and their `second_` counterparts
- Vector-space laws: `add_commutative`, `add_associative`, `add_zero`,
  `add_negate`, `subtract_add`, `subtract_self`, `add_subtract_left`,
  `add_subtract_cancel`, `scale_add`, `scale_scale`, `scale_one`
- Affine laws: `translate_zero`, `translate_translate`,
  `translate_difference` (the action is transitive),
  `difference_translate` and `translate_injective` (it is free),
  `difference_self`
- Bilinear forms: `innerProduct_symmetric`, `innerProduct_add_left`,
  `innerProduct_scale_left`, `innerProduct_self_nonneg`,
  `innerProduct_add_self`; `determinant_antisymmetric`, `determinant_self`,
  `determinant_add_left`, `determinant_scale_left`
- **`lagrange_identity`** — `⟨u,v⟩² + det(u,v)² = ⟨u,u⟩⟨v,v⟩`, a ring
  identity in coordinates — and `cauchy_schwarz` as its corollary
- Metric: `norm_nonneg`, `norm_squared`, `supNorm_LessOrEqual_norm`,
  `norm_LessOrEqual_rootTwo_supNorm` (together, `‖v‖∞ ≤ ‖v‖ ≤ √2·‖v‖∞`),
  `norm_triangle`, `distance_triangle`
- The right-angle turn: `innerProduct_perpendicular` (it is a right
  angle), `perpendicular_perpendicular` (twice reverses), and
  **`determinant_perpendicular`** — `det(v, v⊥) = ⟨v, v⟩`, the identity
  the strip lemma runs on

## The Euclidean norm is primary

`Real.square_root` takes the nonnegativity of its argument as an
argument. That obligation is discharged **once**, in the definition of
`Plane.Vector.norm`, out of `innerProduct_self_nonneg`. Downstream
`norm(v)` takes only `v` and no proof term ever appears at a call site —
a mathematician does not think twice before writing ‖v‖, and neither
should a proof here.

Estimates go through `norm_squared` (`‖v‖·‖v‖ = ⟨v,v⟩`) rather than
through the root itself, and `Real.LessOrEqual_of_square_LessOrEqual`
turns a comparison of squares back into a comparison of values. The sup
norm sits alongside for the axis-parallel squares the polygonal work is
built on.

## Orientation instead of angles

`Plane.Vector.determinant(u, v) = u₁v₂ - u₂v₁`, and its **sign** is the
orientation of the pair — Sedgewick's `ccw`. The Jordan–Schönflies
development uses it wherever a textbook would use an angle, which is why
nothing here needs trigonometry: the library has sine and cosine only as
power series, with no π and no periodicity. `innerProduct(v, v)` serves
as the squared length; no square root is taken.

## How proofs here go

Every law is proved the same way, and new ones should follow it:

```math
Plane.Vector.first(u + v)
    = Plane.Vector.first(u) + Plane.Vector.first(v)
    = Plane.Vector.first(v) + Plane.Vector.first(u)
    = Plane.Vector.first(v + u);
-- the same chain for `second`;
done by Plane.Vector.equal_of_coordinates
```

Expand into coordinates, do the real arithmetic, reassemble. The
expansion and reassembly steps are definitional, so they need no `by`;
the auto-prover also closes the real-arithmetic steps at this size, so
`by ring` is not written either. Only the closing
`equal_of_coordinates` is spelled out, because how the two coordinate
equations yield the vector equation is the one step a reader should not
have to guess.

**Do not** state a coordinate goal in unreduced form and hope `ring`
will close it: `ring` treats `Plane.Vector.first(u + v)` as an opaque
atom. Expand first — that is what the chain above is for.

## Which `by` to keep

The redundancy checker flags every citation the auto-prover could have
found itself. The line taken here: **keep the citation when it names a
theorem, drop it when it names a computation.**

So the coordinate expansions and the real arithmetic in `vector.math` are
bare — a mathematician writing "the first coordinate of `u + v` is
`u₁ + v₁`" cites nothing. But `point.math` keeps nearly all of its
citations, because each one names the vector law being transported to
points: translations compose *because* vector addition is associative,
and saying so is the content of the lemma. Every `done by
equal_of_coordinates` / `equal_of_position` stays too — how two
coordinate equations become one vector equation is the step a reader
should not have to reconstruct.

## Friction worth removing

The two coordinate chains in every law are identical up to
`first`/`second`. A `componentwise` tactic — prove the goal for both
coordinates and close by `equal_of_coordinates` — would collapse each
proof to its one interesting line. Roughly two thirds of this file is
that duplication, and the ratio will be worse in the norm and
determinant laws to come.

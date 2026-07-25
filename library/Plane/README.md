# The plane

The Euclidean plane, built for the Jordan–Schönflies development
(`PLAN_JORDAN_SCHOENFLIES.md`). Two types, deliberately kept apart:

- **`Plane.Vector`** — a displacement. Carries the linear structure.
- **`Plane.Point`** — a location. Acted on by vectors, so `p + v` is a
  point and `q - p` is a vector. *(Not yet built; `vector.math` is the
  first file.)*

Keeping them distinct is what makes `p + q` unwritable. The blueprint
already speaks this way — inversion is `a + (x - a)/‖x - a‖²` — and the
types should agree with it.

## Building

```sh
make -j 16 plane      # this area and exactly its transitive imports
```

Not `make library`: that verifies the Algebra/ fifteen-theorem material,
which dominates the wall clock. The `plane` target pulls in 19 of the 546
Algebra files — the bundled-structure basics that `Real`'s field and ring
instances need — and nothing else. A warm run is about two seconds.

## Main definitions

- `Plane.Vector` and its coordinates `Plane.Vector.first` /
  `Plane.Vector.second`, in [vector.math](vector.math)
- `Plane.Vector.make`, `Plane.Vector.zero`, and the operators `+`, `-`
  (binary and unary), and `*` for scaling by a real

## Main theorems

- `Plane.Vector.equal_of_coordinates` — the bridge from coordinate
  arithmetic to vector equations. **Every law goes through it**, and
  consumers should reach for it rather than unfolding to `Product`.
- The coordinate-reduction lemmas `Plane.Vector.first_add`,
  `first_negate`, `first_scale`, `first_subtract`, `first_zero` and their
  `second_` counterparts
- The vector-space laws: `add_commutative`, `add_associative`,
  `add_zero`, `add_negate`, `subtract_add`, `scale_add`, `scale_scale`,
  `scale_one`

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

## Friction worth removing

The two coordinate chains in every law are identical up to
`first`/`second`. A `componentwise` tactic — prove the goal for both
coordinates and close by `equal_of_coordinates` — would collapse each
proof to its one interesting line. Roughly two thirds of this file is
that duplication, and the ratio will be worse in the norm and
determinant laws to come.

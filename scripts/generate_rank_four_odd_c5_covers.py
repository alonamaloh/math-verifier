#!/usr/bin/env python3
"""Generate finite base tables and the 12 selected odd-C5 covers.

The search is an untrusted authoring aid.  Every emitted row contains an
explicit integer vector, and the kernel checks the quadratic-form value.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from classify_rank_four_normal_forms import NamedForm, coordinate_bounds, named_forms  # noqa: E402


ROW_CHUNK_SIZE = 20
TABLE_PREFIX = "rank_four_odd_c5_base_tables_chunk"
COVERS = ROOT / "library/Algebra/rank_four_odd_c5_covers.math"

PARAMETERS = (
    (0, 6),
    (0, 7),
    (1, 3),
    (1, 6),
    (1, 7),
    (2, 8),
    (2, 9),
    (3, 9),
    (3, 10),
    (3, 11),
    (4, 14),
    (4, 15),
)


@dataclass(frozen=True)
class Tail:
    cutoff: int
    residual_core: int
    fourth: int
    shift: int
    correction: int


def form_name(residue: int, corner: int) -> str:
    return f"odd.c5.r{residue}.c{corner}"


def safe_name(residue: int, corner: int) -> str:
    return f"oddC5R{residue}C{corner}"


def expression(residue: int, corner: int) -> str:
    return f"Matrix.squarePlusDoubleSquareOddRankFourRepresentative(5, {residue}, {corner})"


def choose_tail(residue: int, corner: int) -> Tail:
    options: list[tuple[int, int, int, int, int]] = []
    for fourth in range(1, 201):
        product = residue * fourth
        if product % 9:
            continue
        shift = product // 9
        correction = corner * fourth * fourth - 45 * shift * shift
        if correction < 0:
            continue
        residual_core = (7 - correction) % 8
        if residual_core not in (1, 2, 3, 5, 6):
            continue
        numerator = correction + residual_core - 7
        if numerator < 0 or numerator % 8:
            continue
        cutoff = numerator // 8
        if 8 * cutoff + 7 != residual_core + correction:
            continue
        options.append((cutoff, fourth, residual_core, shift, correction))
    assert options, (residue, corner)
    cutoff, fourth, residual_core, shift, correction = min(options)
    return Tail(cutoff, residual_core, fourth, shift, correction)


def integer(value: int) -> str:
    return str(value) if value >= 0 else f"({value} : ℤ)"


def vector_literal(vector: tuple[int, int, int, int]) -> str:
    return "⟨" + ", ".join(integer(value) for value in vector) + "⟩"


def vector_key(vector: tuple[int, int, int, int]) -> tuple[object, ...]:
    return (
        sum(abs(value) for value in vector),
        max(abs(value) for value in vector),
        sum(value < 0 for value in vector),
        vector,
    )


def witnesses(
    form: NamedForm,
    targets: set[int],
) -> dict[int, tuple[int, int, int, int]]:
    if not targets:
        return {}
    maximum = max(targets)
    x_bound, y_bound, z_bound, w_bound = coordinate_bounds(form.matrix, maximum)
    residue, corner = form.parameters

    # Q=x²+partial(y,z,w).  Cache one small triple for each partial value,
    # then match the finitely many squares x².
    minimum_partial = min(targets) - x_bound * x_bound
    triples: dict[int, tuple[int, int, int]] = {}
    for w in range(-w_bound, w_bound + 1):
        for z in range(-z_bound, z_bound + 1):
            for y in range(-y_bound, y_bound + 1):
                partial = (
                    2 * y * y
                    + 2 * y * z
                    + 5 * z * z
                    + 2 * residue * y * w
                    + corner * w * w
                )
                if minimum_partial <= partial <= maximum:
                    triple = (y, z, w)
                    old = triples.get(partial)
                    if old is None or vector_key((0, *triple)) < vector_key((0, *old)):
                        triples[partial] = triple

    result: dict[int, tuple[int, int, int, int]] = {}
    for target in targets:
        candidates: list[tuple[int, int, int, int]] = []
        for x in range(0, x_bound + 1):
            triple = triples.get(target - x * x)
            if triple is not None:
                candidates.append((x, *triple))
                if x:
                    candidates.append((-x, *triple))
        assert candidates, (form.name, target)
        result[target] = min(candidates, key=vector_key)
    return result


def scalar_expression(
    residue: int,
    corner: int,
    vector: tuple[int, int, int, int],
) -> str:
    x, y, z, w = (integer(value) for value in vector)
    return (
        f"{x} * {x} + 2 * ({y} * {y}) + 2 * {y} * {z} + 5 * ({z} * {z}) "
        f"+ 2 * {residue} * {y} * {w} + {corner} * ({w} * {w})"
    )


def table_module(index: int, residue: int, corner: int) -> str:
    form = next(form for form in named_forms() if form.name == form_name(residue, corner))
    tail = choose_tail(residue, corner)
    targets = {8 * b + 7 for b in range(tail.cutoff)}
    table = witnesses(form, targets)
    name = f"Matrix.{safe_name(residue, corner)}_small_base"
    rendered: list[str] = []

    if tail.cutoff == 0:
        rendered.append(
            f"""theorem {name}
        : ∀ (b : ℕ). b ≥ 0 → b < 0 →
          Matrix.Represents({expression(residue, corner)}, ((8 * b + 7 : ℕ) : ℤ)) := {{
    take b : ℕ;
    suppose b ≥ 0;
    suppose b < 0 as impossible;
    False by Natural.not_less_than_zero(b, impossible);
    done
}}
"""
        )
    else:
        for part_index, start in enumerate(range(0, tail.cutoff, ROW_CHUNK_SIZE)):
            end = min(start + ROW_CHUNK_SIZE, tail.cutoff)
            rows: list[str] = []
            for b in range(start, end):
                target = 8 * b + 7
                vector = table[target]
                rows.append(
                    f"""    {scalar_expression(residue, corner, vector)} = ({target} : ℤ) as scalarComputation;
    Matrix.represents_by_witness(A, target := {target}, vector := {vector_literal(vector)},
      computes := Matrix.squarePlusDoubleSquareOddRankFourRepresentative_coordinateTuple_computes(
        scalarComputation := scalarComputation));"""
                )
            rendered.append(
                f"""theorem {name}_part{part_index}
        : ∀ (b : ℕ). b ≥ {start} → b < {end} →
          Matrix.Represents({expression(residue, corner)}, ((8 * b + 7 : ℕ) : ℤ)) := {{
    let A : Matrix(Integer.commutative_ring_bundle, 4, 4) := {expression(residue, corner)};
{chr(10).join(rows)}
    done by finite_check b from {start} until {end}
}}
"""
            )
        rendered.append(
            f"""theorem {name}
        : ∀ (b : ℕ). b ≥ 0 → b < {tail.cutoff} →
          Matrix.Represents({expression(residue, corner)}, ((8 * b + 7 : ℕ) : ℤ)) := {{
    done by finite_check b from 0 until {tail.cutoff}
}}
"""
        )

    return f"""-- Generated by scripts/generate_rank_four_odd_c5_covers.py.  Do not edit.
-- Explicit witnesses below the uniform odd-C5 obstruction tail.

module Algebra.{TABLE_PREFIX}{index}_generated

import Algebra.rank_four_odd_c5_cover

{"".join(rendered)}"""


def base_cover(residue: int, corner: int) -> str:
    tail = choose_tail(residue, corner)
    selected_core = {
        1: "Or.introduceLeft(done)",
        2: "Or.introduceRight(Or.introduceLeft(done))",
        3: "Or.introduceRight(Or.introduceRight(Or.introduceLeft(done)))",
        5: "Or.introduceRight(Or.introduceRight(Or.introduceRight(Or.introduceLeft(done))))",
        6: "Or.introduceRight(Or.introduceRight(Or.introduceRight(Or.introduceRight(done))))",
    }[tail.residual_core]
    return f"""Matrix.oddFive_base_obstruction_cover_of_tail(
      oddConverse,
      residue := {residue}, corner := {corner}, cutoff := {tail.cutoff},
      residualCore := {tail.residual_core}, fourthCoordinate := {tail.fourth},
      shift := {tail.shift}, correction := {tail.correction},
      small := (b : ℕ) ↦ (below : b < {tail.cutoff}) ↦
        Matrix.{safe_name(residue, corner)}_small_base(b, done, below),
      selectedCore := {selected_core}, targetSplit := done,
      shiftReads := done, correctionReads := done)"""


def cover_theorem(residue: int, corner: int) -> str:
    return f"""theorem Matrix.{safe_name(residue, corner)}_universal_of_three_squares_converse
        (converse : Matrix.ThreeSquaresConverse)
        : Matrix.IsUniversal({expression(residue, corner)}) := {{
  Matrix.OddFiveConverse
      by Matrix.odd_five_converse_of_three_squares(converse) as oddConverse;
  done by Matrix.oddFive_universal_of_base_obstruction_cover(
      oddConverse, residue := {residue}, corner := {corner},
      baseCover := {base_cover(residue, corner)})
}}
"""


def selected_chunk_theorem(index: int, forms: tuple[tuple[int, int], ...]) -> str:
    cases = "\n".join(
        f"""    case R = {expression(residue, corner)}:
      done by Matrix.{safe_name(residue, corner)}_universal_of_three_squares_converse(converse)"""
        for residue, corner in forms
    )
    return f"""theorem Matrix.selectedOddC5Chunk{index}_universal_of_three_squares_converse
        (converse : Matrix.ThreeSquaresConverse)
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (selected : Matrix.IsSelectedRankFourOddC5NormalFormChunk{index}(R))
        : Matrix.IsUniversal(R) := {{
  done by cases {{
{cases}
  }}
}}
"""


def covers_module() -> str:
    imports = "\n".join(
        f"import Algebra.{TABLE_PREFIX}{index}_generated"
        for index in range(len(PARAMETERS))
    )
    first_chunk = PARAMETERS[:8]
    second_chunk = PARAMETERS[8:]
    return f"""-- Generated by scripts/generate_rank_four_odd_c5_covers.py.  Do not edit.
-- All 12 selected odd-C5 forms, conditional only on three squares.

module Algebra.rank_four_odd_c5_covers

import Algebra.rank_four_selected_normal_forms_generated
{imports}

{"".join(cover_theorem(*parameters) for parameters in PARAMETERS)}
{selected_chunk_theorem(0, first_chunk)}
{selected_chunk_theorem(1, second_chunk)}
theorem Matrix.selectedOddC5_universal_of_three_squares_converse
        (converse : Matrix.ThreeSquaresConverse)
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (selected : Matrix.IsSelectedRankFourOddC5NormalForm(R))
        : Matrix.IsUniversal(R) := {{
  done by cases {{
    case Matrix.IsSelectedRankFourOddC5NormalFormChunk0(R) as within:
      done by Matrix.selectedOddC5Chunk0_universal_of_three_squares_converse(converse, R, within)
    case Matrix.IsSelectedRankFourOddC5NormalFormChunk1(R) as within:
      done by Matrix.selectedOddC5Chunk1_universal_of_three_squares_converse(converse, R, within)
  }}
}}
"""


def render_outputs() -> dict[Path, str]:
    outputs = {
        ROOT / "library/Algebra" / f"{TABLE_PREFIX}{index}_generated.math":
            table_module(index, residue, corner)
        for index, (residue, corner) in enumerate(PARAMETERS)
    }
    outputs[COVERS] = covers_module()
    return outputs


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = render_outputs()
    generated = set((ROOT / "library/Algebra").glob(f"{TABLE_PREFIX}*_generated.math"))
    generated.add(COVERS)
    stale_extra = generated - set(outputs)

    if args.check:
        stale = [path for path, contents in outputs.items() if not path.exists() or path.read_text() != contents]
        stale.extend(sorted(stale_extra))
        if stale:
            for path in stale:
                print(f"stale generated file: {path}")
            return 1
        print("rank-four-odd-c5-covers-generated-check: PASS")
        return 0

    for path in stale_extra:
        path.unlink()
    for path, contents in outputs.items():
        if not path.exists() or path.read_text() != contents:
            path.write_text(contents)
            print(path.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

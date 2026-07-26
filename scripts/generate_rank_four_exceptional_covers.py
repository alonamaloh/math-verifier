#!/usr/bin/env python3
"""Generate witness tables and covers for the six co-singleton exceptional forms.

The four weighted-d5 forms (s,r,c) in {(0,0,5),(1,1,5),(1,1,9),(1,2,8)} miss
exactly 15; the odd-C4 form (r,c) = (2,7) misses exactly 10.  Each generated
file is a certificate, not trusted computation: every row carries an explicit
integer vector whose value the kernel checks.
"""

from __future__ import annotations

import argparse
from math import isqrt
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from classify_rank_four_normal_forms import named_forms  # noqa: E402
from generate_rank_four_weighted_d5_covers import (  # noqa: E402
    Tail,
    choose_tail,
    integer,
    scalar_expression,
    vector_key,
    vector_literal,
    witnesses,
)

ROW_CHUNK_SIZE = 20
TABLE_PREFIX = "rank_four_exceptional_weighted_d5_tables_chunk"
COVERS = ROOT / "projects/FifteenTheorem/Algebra/rank_four_exceptional_weighted_d5_covers_generated.math"
ODD_TABLES = ROOT / "projects/FifteenTheorem/Algebra/rank_four_exceptional_odd_c4_r2_c7_tables_generated.math"

WEIGHTED_PARAMETERS = ((0, 0, 5), (1, 1, 5), (1, 1, 9), (1, 2, 8))

# Fixed witnesses for 375 = 15·25, one per form (assembly document, table 4.7).
THREE_SEVENTY_FIVE = {
    (0, 0, 5): (0, 5, 1, 8),
    (1, 1, 5): (0, -1, 7, 4),
    (1, 1, 9): (1, 3, -2, 6),
    (1, 2, 8): (0, 3, 5, 4),
}

# The odd-C4 (2,7) form contains x²+2y²+5z² orthogonal to a norm-330 vector;
# its 5-adic tails start at these cutoffs (assembly document, section 3.2).
ODD_TEN_CUTOFF = 13
ODD_FIFTEEN_CUTOFF = 53


def weighted_name(second: int, third: int, corner: int) -> str:
    return f"weightedD5S{second}R{third}C{corner}"


def weighted_expression(second: int, third: int, corner: int) -> str:
    return (
        "Matrix.squarePlusDoublePlusScaledRankFourRepresentative"
        f"(5, {second}, {third}, {corner})"
    )


ODD_EXPRESSION = "Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, 2, 7)"


def odd_value(vector: tuple[int, int, int, int]) -> int:
    x, y, z, w = vector
    return x * x + 2 * y * y + 2 * y * z + 4 * z * z + 4 * y * w + 7 * w * w


def odd_scalar_expression(vector: tuple[int, int, int, int]) -> str:
    x, y, z, w = (integer(value) for value in vector)
    return (
        f"{x} * {x} + 2 * ({y} * {y}) + 2 * {y} * {z} + 4 * ({z} * {z}) "
        f"+ 2 * 2 * {y} * {w} + 7 * ({w} * {w})"
    )


def odd_witnesses(targets: set[int]) -> dict[int, tuple[int, int, int, int]]:
    if not targets:
        return {}
    maximum = max(targets)
    form = next(form for form in named_forms() if form.name == "odd.c4.r2.c7")
    from classify_rank_four_normal_forms import coordinate_bounds

    x_bound, y_bound, z_bound, w_bound = coordinate_bounds(form.matrix, maximum)
    result: dict[int, tuple[int, int, int, int]] = {}
    for w in range(-w_bound, w_bound + 1):
        for z in range(-z_bound, z_bound + 1):
            for y in range(-y_bound, y_bound + 1):
                partial = 2 * y * y + 2 * y * z + 4 * z * z + 4 * y * w + 7 * w * w
                if partial > maximum:
                    continue
                for target in targets:
                    residual = target - partial
                    if residual < 0:
                        continue
                    x = isqrt(residual)
                    if x * x != residual:
                        continue
                    for signed in ((x, y, z, w), (-x, y, z, w)) if x else ((0, y, z, w),):
                        old = result.get(target)
                        if old is None or vector_key(signed) < vector_key(old):
                            result[target] = signed
    assert set(result) == targets, sorted(targets - set(result))
    return result


def prefix_theorem(
    name: str,
    expression: str,
    computes_lemma: str,
    scalar_of_vector,
    obstruction_core: int,
    lower: int,
    cutoff: int,
    table: dict[int, tuple[int, int, int, int]],
) -> str:
    statement = (
        f"        : ∀ (b : ℕ). b ≥ {lower} → b < {cutoff} →\n"
        f"          Matrix.Represents({expression}, "
        f"((25 * b + {obstruction_core} : ℕ) : ℤ))"
    )
    if lower >= cutoff:
        if lower == 0:
            return f"""theorem {name}
{statement} := {{
    take b : ℕ;
    suppose b ≥ 0;
    suppose b < 0 as impossible;
    False by Natural.not_less_than_zero(b, impossible);
    done
}}
"""
        assert lower == cutoff, (name, lower, cutoff)
        return f"""theorem {name}
{statement} := {{
    take b : ℕ;
    suppose b ≥ {lower} as positive;
    suppose b < {cutoff} as impossible;
    {lower} < {lower} by Natural.LessThan.transitive_left({lower}, b, {lower}, positive, impossible)
        as absurd;
    False by Natural.lt_irreflexive({lower}, absurd);
    done
}}
"""

    parts: list[str] = []
    for part_index, start in enumerate(range(lower, cutoff, ROW_CHUNK_SIZE)):
        end = min(start + ROW_CHUNK_SIZE, cutoff)
        rows: list[str] = []
        for b in range(start, end):
            target = 25 * b + obstruction_core
            vector = table[target]
            rows.append(
                f"""    {scalar_of_vector(vector)} = ({target} : ℤ) as scalarComputation;
    Matrix.represents_by_witness(A, target := {target}, vector := {vector_literal(vector)},
      computes := {computes_lemma}(
        scalarComputation := scalarComputation));"""
            )
        parts.append(
            f"""theorem {name}_part{part_index}
        : ∀ (b : ℕ). b ≥ {start} → b < {end} →
          Matrix.Represents({expression}, ((25 * b + {obstruction_core} : ℕ) : ℤ)) := {{
    let A : Matrix(Integer.commutative_ring_bundle, 4, 4) := {expression};
{chr(10).join(rows)}
    done by finite_check b from {start} until {end}
}}
"""
        )
    parts.append(
        f"""theorem {name}
{statement} := {{
    done by finite_check b from {lower} until {cutoff}
}}
"""
    )
    return "".join(parts)


def weighted_table_module(index: int, second: int, third: int, corner: int) -> str:
    form = next(
        form for form in named_forms()
        if form.name == f"weighted.d5.s{second}.r{third}.c{corner}"
    )
    ten = choose_tail(second, third, corner, 10)
    fifteen = choose_tail(second, third, corner, 15)
    targets = {25 * b + 10 for b in range(ten.cutoff)}
    targets |= {25 * b + 15 for b in range(1, fifteen.cutoff)}
    table = witnesses(form, targets)
    computes = (
        "Matrix.squarePlusDoublePlusScaledRankFourRepresentative_coordinateTuple_computes"
    )

    def scalar(vector: tuple[int, int, int, int]) -> str:
        return scalar_expression(second, third, corner, vector)

    rendered = prefix_theorem(
        f"Matrix.{weighted_name(second, third, corner)}_small_ten_base",
        weighted_expression(second, third, corner), computes, scalar,
        10, 0, ten.cutoff, table,
    ) + prefix_theorem(
        f"Matrix.{weighted_name(second, third, corner)}_small_fifteen_base",
        weighted_expression(second, third, corner), computes, scalar,
        15, 1, fifteen.cutoff, table,
    )
    return f"""-- Generated by scripts/generate_rank_four_exceptional_covers.py.  Do not edit.
-- Explicit witnesses for the finite base cases below the uniform 5-adic tails
-- of the exceptional (truant-fifteen) weighted-d5 form ({second},{third},{corner}).

module Algebra.{TABLE_PREFIX}{index}_generated

import Algebra.rank_four_weighted_d5_cover

{rendered}"""


def odd_table_module() -> str:
    targets = {25 * b + 10 for b in range(1, ODD_TEN_CUTOFF)}
    targets |= {25 * b + 15 for b in range(ODD_FIFTEEN_CUTOFF)}
    table = odd_witnesses(targets)
    computes = (
        "Matrix.squarePlusDoubleSquareOddRankFourRepresentative_coordinateTuple_computes"
    )
    rendered = prefix_theorem(
        "Matrix.oddC4R2C7_small_ten_base",
        ODD_EXPRESSION, computes, odd_scalar_expression,
        10, 1, ODD_TEN_CUTOFF, table,
    ) + prefix_theorem(
        "Matrix.oddC4R2C7_small_fifteen_base",
        ODD_EXPRESSION, computes, odd_scalar_expression,
        15, 0, ODD_FIFTEEN_CUTOFF, table,
    )
    return f"""-- Generated by scripts/generate_rank_four_exceptional_covers.py.  Do not edit.
-- Explicit witnesses for the finite base cases below the norm-330 shifted
-- tails of the exceptional (truant-ten) odd-C4 form (r,c) = (2,7).

module Algebra.rank_four_exceptional_odd_c4_r2_c7_tables_generated

import Algebra.rank_four_exceptional_truants

{rendered}"""


def three_seventy_five_theorem(second: int, third: int, corner: int) -> str:
    vector = THREE_SEVENTY_FIVE[(second, third, corner)]
    x, y, z, w = vector
    value = (
        x * x + 2 * y * y + 5 * z * z
        + 2 * second * y * w + 2 * third * z * w + corner * w * w
    )
    assert value == 375, (second, third, corner, value)
    return f"""theorem Matrix.{weighted_name(second, third, corner)}_represents_three_seventy_five
        : Matrix.Represents(
            {weighted_expression(second, third, corner)}, ((375 : ℕ) : ℤ)) := {{
  {scalar_expression(second, third, corner, vector)} = ((375 : ℕ) : ℤ) as scalarComputation;
  done by Matrix.represents_by_witness(
      {weighted_expression(second, third, corner)},
      target := ((375 : ℕ) : ℤ), vector := {vector_literal(vector)},
      computes := Matrix.squarePlusDoublePlusScaledRankFourRepresentative_coordinateTuple_computes(
        scalarComputation := scalarComputation))
}}
"""


def base_cover(second: int, third: int, corner: int, tail: Tail) -> str:
    return f"""Matrix.weightedD5_base_obstruction_cover_of_tail(
        converse,
        secondResidue := {second}, thirdResidue := {third}, corner := {corner},
        obstructionCore := {tail.obstruction_core}, cutoff := {tail.cutoff},
        residualCore := {tail.residual_core}, fourthCoordinate := {tail.fourth},
        secondShift := {tail.second_shift}, thirdShift := {tail.third_shift},
        correction := {tail.correction},
        small := (b : ℕ) ↦ (below : b < {tail.cutoff}) ↦
          Matrix.{weighted_name(second, third, corner)}_small_ten_base(b, done, below),
        residualCoreBelow := done, residualCoreNonzero := done,
        residualCoreNotTen := done, residualCoreNotFifteen := done,
        targetSplit := done, secondShiftReads := done,
        thirdShiftReads := done, correctionReads := done)"""


def positive_base_cover(second: int, third: int, corner: int, tail: Tail) -> str:
    return f"""Matrix.weightedD5_positive_base_obstruction_cover_of_tail(
        converse,
        secondResidue := {second}, thirdResidue := {third}, corner := {corner},
        obstructionCore := {tail.obstruction_core}, cutoff := {tail.cutoff},
        residualCore := {tail.residual_core}, fourthCoordinate := {tail.fourth},
        secondShift := {tail.second_shift}, thirdShift := {tail.third_shift},
        correction := {tail.correction},
        small := (b : ℕ) ↦ (positive : b ≥ 1) ↦ (below : b < {tail.cutoff}) ↦
          Matrix.{weighted_name(second, third, corner)}_small_fifteen_base(b, positive, below),
        residualCoreBelow := done, residualCoreNonzero := done,
        residualCoreNotTen := done, residualCoreNotFifteen := done,
        targetSplit := done, secondShiftReads := done,
        thirdShiftReads := done, correctionReads := done)"""


def cover_theorem(second: int, third: int, corner: int) -> str:
    ten = choose_tail(second, third, corner, 10)
    fifteen = choose_tail(second, third, corner, 15)
    return f"""theorem Matrix.{weighted_name(second, third, corner)}_representsEveryPositiveExceptFifteen
        (converse : Matrix.OneTwoFiveConverse)
        : Matrix.RepresentsEveryPositiveExcept(
            {weighted_expression(second, third, corner)}, 15) :=
  by Matrix.weightedD5_representsEveryPositiveExceptFifteen_of_covers(
      converse, secondResidue := {second}, thirdResidue := {third}, corner := {corner},
      tenCover := {base_cover(second, third, corner, ten)},
      fifteenCover := {positive_base_cover(second, third, corner, fifteen)},
      fifteenTimesTwentyFive :=
        Matrix.{weighted_name(second, third, corner)}_represents_three_seventy_five)
"""


def covers_module() -> str:
    imports = "\n".join(
        f"import Algebra.{TABLE_PREFIX}{index}_generated"
        for index in range(len(WEIGHTED_PARAMETERS))
    )
    rendered = "".join(
        three_seventy_five_theorem(*form) + cover_theorem(*form)
        for form in WEIGHTED_PARAMETERS
    )
    return f"""-- Generated by scripts/generate_rank_four_exceptional_covers.py.  Do not edit.
-- The four exceptional weighted-d5 forms represent every positive integer
-- except 15, conditional only on the exact converse for x²+2y²+5z².

module Algebra.rank_four_exceptional_weighted_d5_covers_generated

import Algebra.rank_four_exceptional_weighted_d5_cover
{imports}

{rendered}"""


def render_outputs() -> dict[Path, str]:
    outputs: dict[Path, str] = {}
    for index, (second, third, corner) in enumerate(WEIGHTED_PARAMETERS):
        outputs[ROOT / "projects/FifteenTheorem/Algebra" / f"{TABLE_PREFIX}{index}_generated.math"] = (
            weighted_table_module(index, second, third, corner)
        )
    outputs[ODD_TABLES] = odd_table_module()
    outputs[COVERS] = covers_module()
    return outputs


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = render_outputs()
    generated = set((ROOT / "projects/FifteenTheorem/Algebra").glob(f"{TABLE_PREFIX}*_generated.math"))
    generated.add(ODD_TABLES)
    generated.add(COVERS)
    stale_extra = generated - set(outputs)

    if args.check:
        stale = [
            path for path, contents in outputs.items()
            if not path.exists() or path.read_text() != contents
        ]
        stale.extend(sorted(stale_extra))
        if stale:
            for path in stale:
                print(f"stale generated file: {path}")
            return 1
        print("rank-four-exceptional-covers-generated-check: PASS")
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

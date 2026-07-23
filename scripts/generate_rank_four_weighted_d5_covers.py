#!/usr/bin/env python3
"""Generate the finite base tables and concrete weighted-d5 cover theorems.

The generated files are certificates, not trusted computation: every row
contains an explicit integer vector and the kernel checks its value.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from math import isqrt
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from classify_rank_four_normal_forms import NamedForm, coordinate_bounds, named_forms  # noqa: E402


TABLE_CHUNK_SIZE = 1
ROW_CHUNK_SIZE = 20
COVER_CHUNK_SIZE = 14
TABLE_PREFIX = "rank_four_weighted_d5_base_tables_chunk"
COVER_PREFIX = "rank_four_weighted_d5_covers_chunk"
AGGREGATE = ROOT / "library/Algebra/rank_four_weighted_d5_covers.math"

PARAMETERS = (
    *((0, 1, corner) for corner in range(5, 11)),
    *((0, 2, corner) for corner in range(5, 11)),
    *((1, 0, corner) for corner in (2, 4, 5, 6, 9, 10)),
    *((1, 1, corner) for corner in (2, 3, 6, 7, 10)),
    *((1, 2, corner) for corner in (4, 5, 6, 9, 10)),
)


@dataclass(frozen=True)
class Tail:
    obstruction_core: int
    cutoff: int
    residual_core: int
    fourth: int
    second_shift: int
    third_shift: int
    correction: int


def form_name(second: int, third: int, corner: int) -> str:
    return f"weighted.d5.s{second}.r{third}.c{corner}"


def safe_name(second: int, third: int, corner: int) -> str:
    return f"weightedD5S{second}R{third}C{corner}"


def expression(second: int, third: int, corner: int) -> str:
    return (
        "Matrix.squarePlusDoublePlusScaledRankFourRepresentative"
        f"(5, {second}, {third}, {corner})"
    )


def choose_tail(second: int, third: int, corner: int, obstruction_core: int) -> Tail:
    completed_coefficient = 10 * corner - 5 * second * second - 2 * third * third
    options: list[tuple[int, int, int, int, int, int]] = []
    for fourth in range(1, 101):
        if second * fourth % 2 or third * fourth % 5:
            continue
        numerator = completed_coefficient * fourth * fourth
        if numerator % 10:
            continue
        correction = numerator // 10
        residual_core = (obstruction_core - correction) % 25
        if residual_core in (0, 10, 15):
            continue
        cutoff = (correction - obstruction_core + residual_core) // 25
        if cutoff < 0:
            cutoff = 0
        if 25 * cutoff + obstruction_core != residual_core + correction:
            continue
        options.append((
            cutoff,
            fourth,
            residual_core,
            second * fourth // 2,
            third * fourth // 5,
            correction,
        ))
    assert options
    cutoff, fourth, residual_core, second_shift, third_shift, correction = min(options)
    return Tail(
        obstruction_core,
        cutoff,
        residual_core,
        fourth,
        second_shift,
        third_shift,
        correction,
    )


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
    second, third, corner = form.parameters

    # Q=x²+partial(y,z,w).  Cache one small triple for each partial value,
    # then test the finitely many possible squares x² against each target.
    minimum_partial = min(targets) - x_bound * x_bound
    triples: dict[int, tuple[int, int, int]] = {}
    for w in range(-w_bound, w_bound + 1):
        for z in range(-z_bound, z_bound + 1):
            for y in range(-y_bound, y_bound + 1):
                partial = (
                    2 * y * y
                    + 5 * z * z
                    + 2 * second * y * w
                    + 2 * third * z * w
                    + corner * w * w
                )
                if minimum_partial <= partial <= maximum:
                    triple = (y, z, w)
                    old = triples.get(partial)
                    if old is None or (
                        sum(abs(value) for value in triple),
                        max(abs(value) for value in triple),
                        sum(value < 0 for value in triple),
                        triple,
                    ) < (
                        sum(abs(value) for value in old),
                        max(abs(value) for value in old),
                        sum(value < 0 for value in old),
                        old,
                    ):
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
    second: int,
    third: int,
    corner: int,
    vector: tuple[int, int, int, int],
) -> str:
    x, y, z, w = (integer(value) for value in vector)
    return (
        f"{x} * {x} + 2 * ({y} * {y}) + 5 * ({z} * {z}) "
        f"+ 2 * {second} * {y} * {w} + 2 * {third} * {z} * {w} "
        f"+ {corner} * ({w} * {w})"
    )


def table_theorem(
    second: int,
    third: int,
    corner: int,
    tail: Tail,
    table: dict[int, tuple[int, int, int, int]],
) -> str:
    label = "ten" if tail.obstruction_core == 10 else "fifteen"
    name = f"Matrix.{safe_name(second, third, corner)}_small_{label}_base"
    if tail.cutoff == 0:
        return f"""theorem {name}
        : ∀ (b : ℕ). b ≥ 0 → b < 0 →
          Matrix.Represents({expression(second, third, corner)}, ((25 * b + {tail.obstruction_core} : ℕ) : ℤ)) := {{
    take b : ℕ;
    suppose b ≥ 0;
    suppose b < 0 as impossible;
    False by Natural.not_less_than_zero(b, impossible);
    done
}}
"""

    parts: list[str] = []
    for part_index, start in enumerate(range(0, tail.cutoff, ROW_CHUNK_SIZE)):
        end = min(start + ROW_CHUNK_SIZE, tail.cutoff)
        rows: list[str] = []
        for b in range(start, end):
            target = 25 * b + tail.obstruction_core
            vector = table[target]
            rows.append(
                f"""    {scalar_expression(second, third, corner, vector)} = ({target} : ℤ) as scalarComputation;
    Matrix.represents_by_witness(A, target := {target}, vector := {vector_literal(vector)},
      computes := Matrix.squarePlusDoublePlusScaledRankFourRepresentative_coordinateTuple_computes(
        scalarComputation := scalarComputation));"""
            )
        parts.append(
            f"""theorem {name}_part{part_index}
        : ∀ (b : ℕ). b ≥ {start} → b < {end} →
          Matrix.Represents({expression(second, third, corner)}, ((25 * b + {tail.obstruction_core} : ℕ) : ℤ)) := {{
    let A : Matrix(Integer.commutative_ring_bundle, 4, 4) := {expression(second, third, corner)};
{chr(10).join(rows)}
    done by finite_check b from {start} until {end}
}}
"""
        )
    parts.append(
        f"""theorem {name}
        : ∀ (b : ℕ). b ≥ 0 → b < {tail.cutoff} →
          Matrix.Represents({expression(second, third, corner)}, ((25 * b + {tail.obstruction_core} : ℕ) : ℤ)) := {{
    done by finite_check b from 0 until {tail.cutoff}
}}
"""
    )
    return "".join(parts)


def table_module(index: int, forms: list[tuple[int, int, int]]) -> str:
    rendered: list[str] = []
    by_name = {form.name: form for form in named_forms()}
    for second, third, corner in forms:
        form = by_name[form_name(second, third, corner)]
        tails = tuple(choose_tail(second, third, corner, core) for core in (10, 15))
        targets = {
            25 * b + tail.obstruction_core
            for tail in tails
            for b in range(tail.cutoff)
        }
        table = witnesses(form, targets)
        rendered.extend(table_theorem(second, third, corner, tail, table) for tail in tails)
    return f"""-- Generated by scripts/generate_rank_four_weighted_d5_covers.py.  Do not edit.
-- Explicit witnesses for the finite base cases below the uniform 5-adic tails.

module Algebra.{TABLE_PREFIX}{index}_generated

import Algebra.rank_four_weighted_d5_cover

{"".join(rendered)}"""


def small_name(second: int, third: int, corner: int, core: int) -> str:
    label = "ten" if core == 10 else "fifteen"
    return f"Matrix.{safe_name(second, third, corner)}_small_{label}_base"


def base_cover(second: int, third: int, corner: int, tail: Tail) -> str:
    return f"""Matrix.weightedD5_base_obstruction_cover_of_tail(
      converse,
      secondResidue := {second}, thirdResidue := {third}, corner := {corner},
      obstructionCore := {tail.obstruction_core}, cutoff := {tail.cutoff},
      residualCore := {tail.residual_core}, fourthCoordinate := {tail.fourth},
      secondShift := {tail.second_shift}, thirdShift := {tail.third_shift},
      correction := {tail.correction},
      small := (b : ℕ) ↦ (below : b < {tail.cutoff}) ↦
        {small_name(second, third, corner, tail.obstruction_core)}(b, done, below),
      residualCoreBelow := done, residualCoreNonzero := done,
      residualCoreNotTen := done, residualCoreNotFifteen := done,
      targetSplit := done, secondShiftReads := done,
      thirdShiftReads := done, correctionReads := done)"""


def cover_theorem(second: int, third: int, corner: int) -> str:
    ten = choose_tail(second, third, corner, 10)
    fifteen = choose_tail(second, third, corner, 15)
    return f"""theorem Matrix.{safe_name(second, third, corner)}_universal_of_one_two_five_converse
        (converse : Matrix.OneTwoFiveConverse)
        : Matrix.IsUniversal({expression(second, third, corner)}) :=
  by Matrix.weightedD5_universal_of_base_obstruction_covers(
      converse, secondResidue := {second}, thirdResidue := {third}, corner := {corner},
      tenCover := {base_cover(second, third, corner, ten)},
      fifteenCover := {base_cover(second, third, corner, fifteen)})
"""


def cover_module(index: int, forms: list[tuple[int, int, int]]) -> str:
    table_chunks = sorted({PARAMETERS.index(form) // TABLE_CHUNK_SIZE for form in forms})
    imports = "\n".join(
        f"import Algebra.{TABLE_PREFIX}{chunk}_generated"
        for chunk in table_chunks
    )
    return f"""-- Generated by scripts/generate_rank_four_weighted_d5_covers.py.  Do not edit.
-- Concrete conditional universality theorems for one weighted-d5 chunk.

module Algebra.{COVER_PREFIX}{index}

{imports}

{"".join(cover_theorem(*form) for form in forms)}"""


def aggregate_module(cover_count: int) -> str:
    imports = "\n".join(
        f"import Algebra.{COVER_PREFIX}{index}"
        for index in range(cover_count)
    )
    return f"""-- Algebra/rank_four_weighted_d5_covers.math
--
-- All 33 nonexceptional selected weighted-d5 forms, conditional only on
-- the exact converse for x²+2y²+5z².  The five diagonal covers live in the
-- pre-existing zero-residue aggregate; the other 28 are generated below.

module Algebra.rank_four_weighted_d5_covers

import Algebra.rank_four_weighted_d5_zero_residue_covers
{imports}
"""


def render_outputs() -> dict[Path, str]:
    outputs: dict[Path, str] = {}
    forms = list(PARAMETERS)
    for index in range(0, len(forms), TABLE_CHUNK_SIZE):
        chunk_index = index // TABLE_CHUNK_SIZE
        outputs[ROOT / "library/Algebra" / f"{TABLE_PREFIX}{chunk_index}_generated.math"] = table_module(
            chunk_index, forms[index:index + TABLE_CHUNK_SIZE]
        )
    cover_count = 0
    for index in range(0, len(forms), COVER_CHUNK_SIZE):
        chunk_index = index // COVER_CHUNK_SIZE
        outputs[ROOT / "library/Algebra" / f"{COVER_PREFIX}{chunk_index}.math"] = cover_module(
            chunk_index, forms[index:index + COVER_CHUNK_SIZE]
        )
        cover_count += 1
    outputs[AGGREGATE] = aggregate_module(cover_count)
    return outputs


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = render_outputs()
    generated = set((ROOT / "library/Algebra").glob(f"{TABLE_PREFIX}*_generated.math"))
    generated.update((ROOT / "library/Algebra").glob(f"{COVER_PREFIX}*.math"))
    generated.add(AGGREGATE)
    stale_extra = generated - set(outputs)

    if args.check:
        stale = [path for path, contents in outputs.items() if not path.exists() or path.read_text() != contents]
        stale.extend(sorted(stale_extra))
        if stale:
            for path in stale:
                print(f"stale generated file: {path}")
            return 1
        print("rank-four-weighted-d5-covers-generated-check: PASS")
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

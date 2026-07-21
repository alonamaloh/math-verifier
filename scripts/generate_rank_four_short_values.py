#!/usr/bin/env python3
"""Generate checked witnesses through 15 for the 201 regular rank-four forms."""

from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from classify_rank_four_normal_forms import NamedForm, classify, named_forms, vectors_by_norm  # noqa: E402
from generate_rank_four_global_classification import (  # noqa: E402
    CHUNK_SIZE,
    FAMILIES,
    FAMILY_DEFINITIONS,
    or_intro,
    safe_name,
)
from generate_rank_four_isometry_certificates import form_expression  # noqa: E402


OUTPUT = ROOT / "library/Algebra/rank_four_short_values_generated.math"
TABLE_GLOB = "rank_four_short_values_*_chunk*_generated.math"
EXCEPTIONAL_NAMES = (
    "odd.c4.r0.c3",
    "odd.c4.r2.c7",
    "weighted.d5.s0.r0.c5",
    "weighted.d5.s1.r1.c5",
    "weighted.d5.s1.r1.c9",
    "weighted.d5.s1.r2.c8",
)


def theorem_name(form: NamedForm) -> str:
    return f"Matrix.rankFourRepresentsThroughFifteen_{safe_name(form.name)}"


def vector_literal(vector: tuple[int, int, int, int]) -> str:
    return "⟨" + ", ".join(str(value) for value in vector) + "⟩"


def integer(value: int) -> str:
    # Ground scalar certificates have no variable to seed the carrier.  A
    # negative literal therefore needs the one cast that carries real type
    # information; all nonnegative literals remain inferred from the RHS.
    return str(value) if value >= 0 else f"({value} : ℤ)"


def choose_witness(form: NamedForm, target: int) -> tuple[int, int, int, int]:
    candidates = vectors_by_norm(form.matrix, 15)[target]
    assert candidates
    return min(candidates, key=lambda vector: (
        sum(abs(value) for value in vector),
        max(abs(value) for value in vector),
        sum(value < 0 for value in vector),
        vector,
    ))


def scalar_certificate(form: NamedForm, target: int, vector: tuple[int, int, int, int]) -> tuple[str, str]:
    x, y, z, w = (integer(value) for value in vector)
    if form.family == "pilot":
        _, a, b, c = form.parameters
        expression = (
            f"{x} * {x} + {y} * {y} + {z} * {z} + 2 * {integer(a)} * {x} * {w} + 2 * {integer(b)} * {y} * {w} "
            f"+ 2 * {integer(c)} * {z} * {w} + 7 * ({w} * {w})"
        )
        theorem = "Matrix.sumOfThreeSquaresRankFourCandidate_coordinateTuple_computes"
    elif form.family in ("triple", "double"):
        d = 3 if form.family == "triple" else 2
        residue, corner = form.parameters
        expression = f"{x} * {x} + {y} * {y} + {d} * ({z} * {z}) + 2 * {integer(residue)} * {z} * {w} + {corner} * ({w} * {w})"
        theorem = "Matrix.sumOfTwoSquaresPlusScaledSquareRankFourRepresentative_coordinateTuple_computes"
    elif form.family.startswith("weighted.d"):
        d = int(form.family.removeprefix("weighted.d"))
        second, third, corner = form.parameters
        expression = (
            f"{x} * {x} + 2 * ({y} * {y}) + {d} * ({z} * {z}) + 2 * {integer(second)} * {y} * {w} "
            f"+ 2 * {integer(third)} * {z} * {w} + {corner} * ({w} * {w})"
        )
        theorem = "Matrix.squarePlusDoublePlusScaledRankFourRepresentative_coordinateTuple_computes"
    elif form.family.startswith("odd.c"):
        form_corner = int(form.family.removeprefix("odd.c"))
        residue, corner = form.parameters
        expression = (
            f"{x} * {x} + 2 * ({y} * {y}) + 2 * {y} * {z} + {form_corner} * ({z} * {z}) "
            f"+ 2 * {integer(residue)} * {y} * {w} + {corner} * ({w} * {w})"
        )
        theorem = "Matrix.squarePlusDoubleSquareOddRankFourRepresentative_coordinateTuple_computes"
    else:
        raise ValueError(form.family)
    assert sum(vector[i] * form.matrix[i][j] * vector[j] for i in range(4) for j in range(4)) == target
    return expression, theorem


def witness_row(form: NamedForm, target: int) -> str:
    vector = choose_witness(form, target)
    expression, computes_theorem = scalar_certificate(form, target, vector)
    return f"""    {expression} = ({target} : ℤ) as scalarComputation;
    Matrix.represents_by_witness(A, target := {target}, vector := {vector_literal(vector)},
      computes := {computes_theorem}(scalarComputation := scalarComputation));"""


def render_table(form: NamedForm) -> str:
    rows = "\n".join(witness_row(form, target) for target in range(1, 16))
    return f"""theorem {theorem_name(form)}
        : ∀ (s : ℕ). s ≥ 1 → s < 16 → Matrix.Represents({form_expression(form)}, (s : ℤ)) := {{
    let A : Matrix(Integer.commutative_ring_bundle, 4, 4) := {form_expression(form)};
{rows}
    done by finite_check s from 1 until 16
}}
"""


def exceptional_proof(form: NamedForm, equality_name: str) -> str:
    index = EXCEPTIONAL_NAMES.index(form.name)
    expression = form_expression(form)
    proof = or_intro(
        index,
        len(EXCEPTIONAL_NAMES),
        f"reflexivity(Matrix(Integer.commutative_ring_bundle, 4, 4), {expression})",
    )
    return f"""Matrix.IsExceptionalRankFourNormalForm({expression}) by {proof} as concreteExceptional;
      {expression} = R by {equality_name} as reverseReads;
      Matrix.IsExceptionalRankFourNormalForm(R) by Equality.transport_proposition(
        (candidate : Matrix(Integer.commutative_ring_bundle, 4, 4)) ↦ Matrix.IsExceptionalRankFourNormalForm(candidate),
        {expression}, R, reverseReads, concreteExceptional) as outcome;
      done by disjunct(outcome)"""


def regular_proof(form: NamedForm, equality_name: str) -> str:
    expression = form_expression(form)
    return f"""Matrix.RepresentsThroughFifteen({expression}) by {theorem_name(form)} as concreteRepresents;
      {expression} = R by {equality_name} as reverseReads;
      Matrix.RepresentsThroughFifteen(R) by Equality.transport_proposition(
        (candidate : Matrix(Integer.commutative_ring_bundle, 4, 4)) ↦ Matrix.RepresentsThroughFifteen(candidate),
        {expression}, R, reverseReads, concreteRepresents) as outcome;
      done by disjunct(outcome)"""


def chunk_name(family: str, index: int) -> str:
    return f"Matrix.rankFourShortValues_{safe_name(family)}_chunk{index}"


def table_module_name(family: str, index: int) -> str:
    return f"Algebra.rank_four_short_values_{safe_name(family)}_chunk{index}_generated"


def table_output(family: str, index: int) -> Path:
    return ROOT / "library/Algebra" / f"rank_four_short_values_{safe_name(family)}_chunk{index}_generated.math"


def render_table_module(family: str, index: int, chunk: list[NamedForm]) -> str:
    regular = [form for form in chunk if form.name not in EXCEPTIONAL_NAMES]
    tables = "\n".join(render_table(form) for form in regular)
    return f"""-- Generated by scripts/generate_rank_four_short_values.py.  Do not edit.
-- Explicit witnesses through 15 for one parallel rank-four certificate chunk.

module {table_module_name(family, index)}

import Algebra.rank_four_short_values

{tables}"""


def render_chunk(family: str, index: int, chunk: list[NamedForm]) -> str:
    if len(chunk) == 1:
        form = chunk[0]
        body = exceptional_proof(form, "formReads") if form.name in EXCEPTIONAL_NAMES else regular_proof(form, "formReads")
        indented_body = "\n".join(f"  {line}" for line in body.splitlines())
        return f"""theorem {chunk_name(family, index)}
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (selected : {FAMILY_DEFINITIONS[family]}Chunk{index}(R))
        : Matrix.IsExceptionalRankFourNormalForm(R) ∨ Matrix.RepresentsThroughFifteen(R) := {{
  R = {form_expression(form)} by selected as formReads;
{indented_body}
}}
"""
    cases = []
    for form in chunk:
        body = exceptional_proof(form, "formReads") if form.name in EXCEPTIONAL_NAMES else regular_proof(form, "formReads")
        cases.append(f"""    case R = {form_expression(form)} as formReads: {{
      {body}
    }}""")
    return f"""theorem {chunk_name(family, index)}
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (selected : {FAMILY_DEFINITIONS[family]}Chunk{index}(R))
        : Matrix.IsExceptionalRankFourNormalForm(R) ∨ Matrix.RepresentsThroughFifteen(R) := {{
  done by cases {{
{chr(10).join(cases)}
  }}
}}
"""


def family_name(family: str) -> str:
    return f"Matrix.rankFourShortValues_{safe_name(family)}"


def render_family(family: str, chunks: list[list[NamedForm]]) -> str:
    if len(chunks) == 1:
        body = f"done by {chunk_name(family, 0)}(selected := selected)"
    else:
        cases = "\n".join(
            f"    case {FAMILY_DEFINITIONS[family]}Chunk{index}(R) as within: "
            f"done by {chunk_name(family, index)}(selected := within)"
            for index in range(len(chunks))
        )
        body = f"""done by cases {{
{cases}
  }}"""
    return f"""theorem {family_name(family)}
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (selected : {FAMILY_DEFINITIONS[family]}(R))
        : Matrix.IsExceptionalRankFourNormalForm(R) ∨ Matrix.RepresentsThroughFifteen(R) := {{
  {body}
}}
"""


def render_global() -> str:
    cases = "\n".join(
        f"    case {FAMILY_DEFINITIONS[family]}(R) as within: "
        f"done by {family_name(family)}(selected := within)"
        for family in FAMILIES
    )
    return f"""theorem Matrix.selectedRankFour_short_value_classification
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (selected : Matrix.IsSelectedRankFourNormalForm(R))
        : Matrix.IsExceptionalRankFourNormalForm(R) ∨ Matrix.RepresentsThroughFifteen(R) := {{
  done by cases {{
{cases}
  }}
}}

theorem Matrix.rankFourEscalatorRepresentative_short_value_classification
        (B : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (classified : Matrix.IsRankFourEscalatorRepresentative(B))
        : (Matrix.truant(B) = 10 ∨ Matrix.truant(B) = 15)
          ∨ Matrix.RepresentsThroughFifteen(B) := {{
  choose R such that Matrix.IsSelectedRankFourNormalForm(R) ∧ Matrix.IsIsometric(B, R) from classified;
  Matrix.IsSelectedRankFourNormalForm(R)
      by And.left(Matrix.IsSelectedRankFourNormalForm(R), Matrix.IsIsometric(B, R)) as selected;
  Matrix.IsIsometric(B, R)
      by And.right(Matrix.IsSelectedRankFourNormalForm(R), Matrix.IsIsometric(B, R)) as isometric;
  Matrix.IsExceptionalRankFourNormalForm(R) ∨ Matrix.RepresentsThroughFifteen(R)
      by Matrix.selectedRankFour_short_value_classification(selected := selected);
  done by cases {{
    case Matrix.IsExceptionalRankFourNormalForm(R) as exceptional: {{
      Matrix.truant(B) = 10 ∨ Matrix.truant(B) = 15
          by Matrix.isometric_exceptional_rankFour_truant(isometric := isometric, exceptional := exceptional) as truantReads;
      done by disjunct(truantReads)
    }}
    case Matrix.RepresentsThroughFifteen(R) as represents: {{
      Matrix.RepresentsThroughFifteen(B)
          by Matrix.isometric_representsThroughFifteen(isometric := isometric, targetRepresents := represents) as outcome;
      done by disjunct(outcome)
    }}
  }}
}}

theorem Matrix.escalator_rank_four_short_value_classification
        (B : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (escalator : Matrix.IsEscalator(4, B))
        : (Matrix.truant(B) = 10 ∨ Matrix.truant(B) = 15)
          ∨ Matrix.RepresentsThroughFifteen(B) := {{
  Matrix.IsRankFourEscalatorRepresentative(B) by Matrix.escalator_rank_four(escalator := escalator);
  done by Matrix.rankFourEscalatorRepresentative_short_value_classification
}}
"""


def render_outputs() -> dict[Path, str]:
    representatives, _ = classify(named_forms(), theta_limit=15)
    assert len(representatives) == 207
    exceptional = {form.name for form in representatives if any(not vectors_by_norm(form.matrix, 15)[n] for n in range(1, 16))}
    assert exceptional == set(EXCEPTIONAL_NAMES)
    regular = [form for form in representatives if form.name not in exceptional]
    assert len(regular) == 201

    grouped: dict[str, list[NamedForm]] = defaultdict(list)
    for form in representatives:
        grouped[form.family].append(form)
    chunks_by_family = {
        family: [grouped[family][index:index + CHUNK_SIZE] for index in range(0, len(grouped[family]), CHUNK_SIZE)]
        for family in FAMILIES
    }
    table_outputs = {
        table_output(family, index): render_table_module(family, index, chunk)
        for family in FAMILIES
        for index, chunk in enumerate(chunks_by_family[family])
    }
    chunks = "\n".join(
        render_chunk(family, index, chunk)
        for family in FAMILIES
        for index, chunk in enumerate(chunks_by_family[family])
    )
    families = "\n".join(render_family(family, chunks_by_family[family]) for family in FAMILIES)
    imports = "\n".join(
        f"import {table_module_name(family, index)}"
        for family in FAMILIES
        for index in range(len(chunks_by_family[family]))
    )
    classification = f"""-- Algebra/rank_four_short_values_generated.math
-- Generated by scripts/generate_rank_four_short_values.py.  Do not edit.
-- 3,015 explicit witnesses certify values 1 through 15 for the 201
-- non-exceptional selected normal forms.  The witness tables live in small
-- imported chunks so the ordinary parallel library build can check them.

module Algebra.rank_four_short_values_generated

{imports}

{chunks}
{families}
{render_global()}"""
    return {OUTPUT: classification, **table_outputs}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = render_outputs()
    actual_table_paths = set((ROOT / "library/Algebra").glob(TABLE_GLOB))
    expected_table_paths = set(expected) - {OUTPUT}
    if args.check:
        stale = [path for path, contents in expected.items() if not path.exists() or path.read_text() != contents]
        stale.extend(sorted(actual_table_paths - expected_table_paths))
        if stale:
            for path in stale:
                print(f"stale generated file: {path}")
            return 1
        print("rank-four-short-values-generated-check: PASS")
        return 0
    for stale_path in actual_table_paths - expected_table_paths:
        stale_path.unlink()
    for path, contents in expected.items():
        if not path.exists() or path.read_text() != contents:
            path.write_text(contents)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

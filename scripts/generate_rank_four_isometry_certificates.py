#!/usr/bin/env python3
"""Generate kernel-checkable certificates for the 69 rank-four identifications."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

from classify_rank_four_normal_forms import (
    Identification,
    Matrix,
    classify,
    inverse_unimodular,
    named_forms,
)


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "library/Algebra/rank_four_isometry_certificates_generated.math"


def integer(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def matrix_literal(matrix: Matrix) -> str:
    rows = [", ".join(integer(value) for value in row) for row in matrix]
    return "Matrix.fourByFour(\n      " + ",\n      ".join(rows) + ")"


def coordinate_tuple(entries: list[str]) -> str:
    return "(⟨" + ", ".join(entries) + "⟩ : RingVector(Integer.commutative_ring_bundle, 4))"


def linear_action(matrix: Matrix, vector: list[str]) -> list[str]:
    return [
        " + ".join(f"{integer(matrix[i][j])}*({vector[j]})" for j in range(4))
        for i in range(4)
    ]


def named_expressions(prefix: str, expressions: list[str], indent: str = "      ") -> tuple[list[str], str]:
    names = [f"{prefix}{i}" for i in range(4)]
    declarations = "\n".join(f"{indent}let {names[i]} : ℤ := {expressions[i]};" for i in range(4))
    return names, declarations


def form_expression(identification_form) -> str:
    family = identification_form.family
    parameters = identification_form.parameters
    if family == "pilot":
        _, a, b, c = parameters
        return f"Matrix.sumOfThreeSquaresRankFourCandidate({integer(a)}, {integer(b)}, {integer(c)})"
    if family == "triple":
        residue, corner = parameters
        return f"Matrix.sumOfTwoSquaresPlusScaledSquareRankFourRepresentative(3, {integer(residue)}, {corner})"
    if family == "double":
        residue, corner = parameters
        return f"Matrix.sumOfTwoSquaresPlusScaledSquareRankFourRepresentative(2, {integer(residue)}, {corner})"
    if family.startswith("weighted.d"):
        d = int(family.removeprefix("weighted.d"))
        second, third, corner = parameters
        return (
            "Matrix.squarePlusDoublePlusScaledRankFourRepresentative"
            f"({d}, {integer(second)}, {integer(third)}, {corner})"
        )
    if family.startswith("odd.c"):
        form_corner = int(family.removeprefix("odd.c"))
        residue, corner = parameters
        return (
            "Matrix.squarePlusDoubleSquareOddRankFourRepresentative"
            f"({form_corner}, {integer(residue)}, {corner})"
        )
    raise ValueError(family)


def form_action(form, vector: list[str]) -> list[str]:
    family = form.family
    parameters = form.parameters
    x0, x1, x2, x3 = (f"({entry})" for entry in vector)
    if family == "pilot":
        _, a, b, c = parameters
        return [
            f"{x0} + {integer(a)}*{x3}",
            f"{x1} + {integer(b)}*{x3}",
            f"{x2} + {integer(c)}*{x3}",
            f"{integer(a)}*{x0} + {integer(b)}*{x1} + {integer(c)}*{x2} + 7*{x3}",
        ]
    if family in ("triple", "double"):
        d = 3 if family == "triple" else 2
        residue, corner = parameters
        return [x0, x1, f"{d}*{x2} + {integer(residue)}*{x3}", f"{integer(residue)}*{x2} + {corner}*{x3}"]
    if family.startswith("weighted.d"):
        d = int(family.removeprefix("weighted.d"))
        second, third, corner = parameters
        return [
            x0,
            f"2*{x1} + {integer(second)}*{x3}",
            f"{d}*{x2} + {integer(third)}*{x3}",
            f"{integer(second)}*{x1} + {integer(third)}*{x2} + {corner}*{x3}",
        ]
    if family.startswith("odd.c"):
        form_corner = int(family.removeprefix("odd.c"))
        residue, corner = parameters
        return [
            x0,
            f"2*{x1} + {x2} + {integer(residue)}*{x3}",
            f"{x1} + {form_corner}*{x2}",
            f"{integer(residue)}*{x1} + {corner}*{x3}",
        ]
    raise ValueError(family)


def action_theorem(form) -> str:
    if form.family == "pilot":
        return "Matrix.sumOfThreeSquaresRankFourCandidate_apply_coordinateTuple"
    if form.family in ("triple", "double"):
        return "Matrix.sumOfTwoSquaresPlusScaledSquareRankFourRepresentative_apply_coordinateTuple"
    if form.family.startswith("weighted.d"):
        return "Matrix.squarePlusDoublePlusScaledRankFourRepresentative_apply_coordinateTuple"
    if form.family.startswith("odd.c"):
        return "Matrix.squarePlusDoubleSquareOddRankFourRepresentative_apply_coordinateTuple"
    raise ValueError(form.family)


def vector_equality(left: list[str], right: list[str], indent: str) -> str:
    names = ("first", "second", "third", "fourth")
    claims = "\n".join(f"{indent}{left[i]} = {right[i]} by ring as {names[i]};" for i in range(4))
    arguments = ", ".join(f"{name} := {name}" for name in names)
    return f"{{\n{claims}\n{indent}done by RingVector.fourCoordinates_equal({arguments})\n{indent[:-2]}}}"


def vector_decomposition(indent: str = "      ") -> str:
    return f"""let x0 : ℤ := x(NaturalsBelow.firstOfFour);
{indent}let x1 : ℤ := x(NaturalsBelow.secondOfFour);
{indent}let x2 : ℤ := x(NaturalsBelow.thirdOfFour);
{indent}let x3 : ℤ := x(NaturalsBelow.fourthOfFour);
{indent}x = {coordinate_tuple(["x0", "x1", "x2", "x3"])} by RingVector.eq_fourCoordinates as xReads;"""


def render_inverse_action(outer_name: str, outer: Matrix, inner_name: str, inner: Matrix) -> str:
    variables = ["x0", "x1", "x2", "x3"]
    inner_result, inner_lets = named_expressions("y", linear_action(inner, variables))
    outer_result, outer_lets = named_expressions("z", linear_action(outer, inner_result))
    return f"""(x : RingVector(Integer.commutative_ring_bundle, 4)) ↦ {{
      {vector_decomposition()}
{inner_lets}
{outer_lets}
      {inner_name} · {coordinate_tuple(variables)} = {coordinate_tuple(inner_result)}
          by Matrix.fourByFour_apply_coordinateTuple as innerAction;
      {outer_name} · {coordinate_tuple(inner_result)} = {coordinate_tuple(outer_result)}
          by Matrix.fourByFour_apply_coordinateTuple as outerAction;
      {outer_name} · ({inner_name} · x)
         = {outer_name} · ({inner_name} · {coordinate_tuple(variables)}) by substituting xReads
         = {outer_name} · {coordinate_tuple(inner_result)} by substituting innerAction
         = {coordinate_tuple(outer_result)} by outerAction
         = {coordinate_tuple(variables)} by {vector_equality(outer_result, variables, "           ")}
         = x by Equality.symmetry(xReads);
      done
    }}"""


def render_pullback(identification: Identification) -> str:
    source = identification.source
    target = identification.representative
    change = identification.change_of_basis
    variables = ["x0", "x1", "x2", "x3"]
    changed, change_lets = named_expressions("y", linear_action(change, variables))
    source_result, source_lets = named_expressions("z", form_action(source, changed))
    pulled, pullback_lets = named_expressions(
        "w", linear_action(tuple(zip(*change)), source_result)  # type: ignore[arg-type]
    )
    target_result, target_lets = named_expressions("t", form_action(target, variables))
    return f"""(x : RingVector(Integer.commutative_ring_bundle, 4)) ↦ {{
      {vector_decomposition()}
{change_lets}
{source_lets}
{pullback_lets}
{target_lets}
      U · {coordinate_tuple(variables)} = {coordinate_tuple(changed)}
          by Matrix.fourByFour_apply_coordinateTuple as changeAction;
      source · {coordinate_tuple(changed)} = {coordinate_tuple(source_result)}
          by {action_theorem(source)} as sourceAction;
      Uᵀ · {coordinate_tuple(source_result)} = {coordinate_tuple(pulled)}
          by Matrix.fourByFour_transpose_apply_coordinateTuple as transposeAction;
      target · {coordinate_tuple(variables)} = {coordinate_tuple(target_result)}
          by {action_theorem(target)} as targetAction;
      Uᵀ · (source · (U · x))
         = Uᵀ · (source · (U · {coordinate_tuple(variables)})) by substituting xReads
         = Uᵀ · (source · {coordinate_tuple(changed)}) by substituting changeAction
         = Uᵀ · {coordinate_tuple(source_result)} by substituting sourceAction
         = {coordinate_tuple(pulled)} by transposeAction
         = {coordinate_tuple(target_result)} by {vector_equality(pulled, target_result, "           ")}
         = target · {coordinate_tuple(variables)} by Equality.symmetry(targetAction)
         = target · x by substituting xReads;
      done
    }}"""


def theorem_name(identification: Identification) -> str:
    source = re.sub(r"[^A-Za-z0-9]+", "_", identification.source.name).strip("_")
    target = re.sub(r"[^A-Za-z0-9]+", "_", identification.representative.name).strip("_")
    return f"Matrix.rankFourGlobalIsometry_{source}_to_{target}"


def render_certificate(identification: Identification) -> str:
    change = identification.change_of_basis
    inverse = inverse_unimodular(change)
    return f"""automatic theorem {theorem_name(identification)}
        : Matrix.IsIsometric({form_expression(identification.source)},
            {form_expression(identification.representative)}) := {{
  let source : Matrix(Integer.commutative_ring_bundle, 4, 4) := {form_expression(identification.source)};
  let target : Matrix(Integer.commutative_ring_bundle, 4, 4) := {form_expression(identification.representative)};
  let U : Matrix(Integer.commutative_ring_bundle, 4, 4) := {matrix_literal(change)};
  let V : Matrix(Integer.commutative_ring_bundle, 4, 4) := {matrix_literal(inverse)};
  done by Matrix.isometric_of_inverse_and_pullback_actions(
    A := source, B := target, U := U, V := V,
    forwardInverse := {render_inverse_action("U", change, "V", inverse)},
    backwardInverse := {render_inverse_action("V", inverse, "U", change)},
    pullback := {render_pullback(identification)})
}}
"""


def identifications() -> list[Identification]:
    _, result = classify(named_forms(), theta_limit=15)
    assert len(result) == 69
    return result


def render() -> str:
    certificates = "\n".join(render_certificate(identification) for identification in identifications())
    return f"""-- Algebra/rank_four_isometry_certificates_generated.math
-- Generated by scripts/generate_rank_four_isometry_certificates.py.  Do not edit.
-- The search is untrusted; these 69 explicit inverse and pullback actions are checked by the kernel.

module Algebra.rank_four_isometry_certificates_generated

import Algebra.rank_four_isometry_certificates

{certificates}"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    generated = render()
    if args.stdout:
        sys.stdout.write(generated)
        return 0
    if args.check:
        if not args.output.exists() or args.output.read_text() != generated:
            print(f"stale generated file: {args.output}", file=sys.stderr)
            return 1
        return 0
    args.output.write_text(generated)
    print(f"wrote {args.output}: {len(identifications())} isometry certificates")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Generate top-shear certificates above x^2 + y^2 + 3z^2.

For A = diag(1, 1, 3) and truant 6, positive-definiteness is equivalent to
3a^2 + 3b^2 + c^2 < 18.  Reducing the first two coordinates to zero and
the third to its balanced residue modulo 3 leaves 18 top-shear normal forms.
The search is untrusted; the generated module kernel-checks every shear.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
OUTPUTS = {
    "certificates": ROOT / "library/Algebra/rank_four_diagonal_branch_generated.math",
    "cases": ROOT / "library/Algebra/rank_four_diagonal_branch_box_cases_generated.math",
    "classifier": ROOT / "library/Algebra/rank_four_diagonal_branch_classification_generated.math",
}


def integer(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def name_coordinate(value: int) -> str:
    return f"m{-value}" if value < 0 else f"p{value}"


def raw_borders() -> list[tuple[int, int, int]]:
    borders = [
        border
        for border in itertools.product(range(-4, 5), repeat=3)
        if 3 * border[0] ** 2 + 3 * border[1] ** 2 + border[2] ** 2 < 18
    ]
    assert len(borders) == 109
    return borders


def reduce_border(border: tuple[int, int, int]) -> tuple[tuple[int, int, int], int]:
    a, b, c = border
    residue = (c + 1) % 3 - 1
    shift = (-a, -b, (residue - c) // 3)
    x, y, z = shift
    corner = 6 + 2 * (a * x + b * y + c * z) + x * x + y * y + 3 * z * z
    return shift, corner


def theorem_name(border: tuple[int, int, int]) -> str:
    return "Matrix.rankFourDiagonalBranch_border_" + "_".join(
        name_coordinate(value) for value in border
    )


def render_certificate(border: tuple[int, int, int]) -> str:
    shift, corner = reduce_border(border)
    a, b, c = map(integer, border)
    x, y, z = map(integer, shift)
    residue = integer(border[2] + 3 * shift[2])
    az, bz, cz = (f"({value} : ℤ)" for value in (a, b, c))
    xz, yz, zz = (f"({value} : ℤ)" for value in (x, y, z))
    residue_z = f"({residue} : ℤ)"
    residue_value = border[2] + 3 * shift[2]
    index = {-1: 0, 0: 6, 1: 12}[residue_value] + corner - 1
    if index == 17:
        introduction = "Or.introduceRight(" * index + "reduced" + ")" * index
    else:
        introduction = "Or.introduceRight(" * index + "Or.introduceLeft(reduced)" + ")" * index
    return f"""automatic theorem {theorem_name(border)}
        : Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourTopShearNormalForm(
            Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate({a}, {b}, {c})) := {{
  {az} + {xz} = 0 by ring as firstVanishes;
  {bz} + {yz} = 0 by ring as secondVanishes;
  {cz} + 3 * {zz} = {residue_z} by ring as thirdReduces;
  (6 : ℤ) + 2 * ({az} * {xz} + {bz} * {yz} + {cz} * {zz})
      + {xz} * {xz} + {yz} * {yz} + 3 * ({zz} * {zz}) = {corner} by ring as cornerReduces;
  Matrix.IsIsometric(
      Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate({a}, {b}, {c}),
      Matrix.sumOfTwoSquaresPlusTripleSquareRankFourRepresentative({residue}, {corner}))
      by Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate_isometric_reduced(
      x := {x}, y := {y}, z := {z}, residue := {residue}, corner := {corner},
      firstVanishes := firstVanishes, secondVanishes := secondVanishes,
      thirdReduces := thirdReduces, cornerReduces := cornerReduces)
  as reduced;
  done by {introduction}
}}
"""


def fixed_name(value: int) -> str:
    return name_coordinate(value)


def render_integer_all_from(
    predicate: str,
    predicate_body: str,
    variable: str,
    start: int,
    stop: int,
    facts: list[tuple[int, str]],
) -> str:
    """Render an AllFrom certificate with every leaf cited explicitly."""
    assert [value for value, _ in facts] == list(range(start, stop))
    count = stop - start
    lines = [f"  let {predicate} : ℤ → Proposition := ({variable} : ℤ) ↦"]
    for index, line in enumerate(predicate_body.splitlines()):
        prefix = "      " if index == 0 else "        "
        lines.append(prefix + line)
    lines[-1] += ";"
    for value, proof in facts:
        lines.append(f"  {predicate}({integer(value)}) by {proof} as at_{fixed_name(value)};")
    lines.append(
        f"  Integer.AllFrom({predicate}, {integer(stop)}, 0) "
        f"by Integer.AllFrom.empty({predicate}, {integer(stop)}) as from_{fixed_name(stop)};"
    )
    for value in reversed(range(start, stop)):
        next_value = value + 1
        remaining = stop - next_value
        lines.append(
            f"  ({integer(next_value)} : ℤ) = ({integer(value)} : ℤ) + 1 by ring as "
            f"step_{fixed_name(value)};"
        )
        lines.append(
            f"  Integer.AllFrom({predicate}, {integer(value)}, {1 + remaining}) by "
            f"Integer.AllFrom.prepend({predicate}, {integer(value)}, {integer(next_value)}, {remaining}, "
            f"step_{fixed_name(value)}, at_{fixed_name(value)}, from_{fixed_name(next_value)}) "
            f"as from_{fixed_name(value)};"
        )
    lines.append(
        f"  ({integer(stop)} : ℤ) = {integer(start)} + ({count} : ℤ) by ring as upperReads;"
    )
    lines.append(f"  take {variable} : ℤ;")
    lines.append(f"  suppose {integer(start)} ≤ {variable} as lower;")
    lines.append(f"  suppose {variable} < {integer(stop)} as upper;")
    lines.append(
        f"  done by Integer.AllFrom_between({predicate}, {integer(start)}, {count}, {integer(stop)}, "
        f"upperReads, from_{fixed_name(start)}, {variable}, lower, upper)"
    )
    return "\n".join(lines)


def render_box_case(a: int, b: int, c: int) -> str:
    name = f"Matrix.rankFourDiagonalBranch_box_case_{fixed_name(a)}_{fixed_name(b)}_{fixed_name(c)}"
    value = 3 * a * a + 3 * b * b + c * c
    statement = f"""automatic theorem {name}
        (bound : 3 * (({a} : ℤ) * {a}) + 3 * (({b} : ℤ) * {b}) + ({c} : ℤ) * {c} < 18)
        : Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourTopShearNormalForm(
            Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate({a}, {b}, {c})) := {{
"""
    border = (a, b, c)
    if value < 18:
        body = f"  done by {theorem_name(border)}\n"
    else:
        body = f"""  3 * (({a} : ℤ) * {a}) + 3 * (({b} : ℤ) * {b}) + ({c} : ℤ) * {c} = {value} by ring as valueReads;
  ({value} : ℤ) < 18 by substituting valueReads;
  (18 : ℤ) ≤ {value};
  ({value} : ℤ) < {value};
  ({value} : ℕ) < {value} by Natural.to_integer.LessThan_reflects;
  False by Natural.lt_irreflexive;
  done
"""
    return statement + body + "}\n"


def render_c_sweep(a: int, b: int) -> str:
    predicate = f"""3 * (({a} : ℤ) * {a}) + 3 * (({b} : ℤ) * {b}) + c * c < 18
          → Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourTopShearNormalForm(
              Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate({a}, {b}, c))"""
    facts = [
        (
            c,
            f"Matrix.rankFourDiagonalBranch_box_case_{fixed_name(a)}_{fixed_name(b)}_{fixed_name(c)}",
        )
        for c in range(-4, 5)
    ]
    certificate = render_integer_all_from("P", predicate, "c", -4, 5, facts)
    return f"""automatic theorem Matrix.rankFourDiagonalBranch_box_{fixed_name(a)}_{fixed_name(b)}_all_c
        : ∀ (c : ℤ). -4 ≤ c → c < 5
          → 3 * (({a} : ℤ) * {a}) + 3 * (({b} : ℤ) * {b}) + c * c < 18
          → Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourTopShearNormalForm(
              Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate({a}, {b}, c)) := {{
{certificate}
}}
"""


def render_b_sweep(a: int) -> str:
    predicate = f"""∀ (c : ℤ). -4 ≤ c → c < 5
          → 3 * (({a} : ℤ) * {a}) + 3 * (b * b) + c * c < 18
          → Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourTopShearNormalForm(
              Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate({a}, b, c))"""
    facts = [
        (b, f"Matrix.rankFourDiagonalBranch_box_{fixed_name(a)}_{fixed_name(b)}_all_c")
        for b in range(-2, 3)
    ]
    certificate = render_integer_all_from("P", predicate, "b", -2, 3, facts)
    return f"""automatic theorem Matrix.rankFourDiagonalBranch_box_{fixed_name(a)}_all_b_c
        : ∀ (b : ℤ). -2 ≤ b → b < 3
          → ∀ (c : ℤ). -4 ≤ c → c < 5
          → 3 * (({a} : ℤ) * {a}) + 3 * (b * b) + c * c < 18
          → Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourTopShearNormalForm(
              Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate({a}, b, c)) := {{
{certificate}
}}
"""


def render_box_cases() -> str:
    return "\n".join(
        render_box_case(a, b, c)
        for a in range(-2, 3)
        for b in range(-2, 3)
        for c in range(-4, 5)
    )


def render_box_classifier() -> str:
    c_sweeps = "\n".join(
        render_c_sweep(a, b) for a in range(-2, 3) for b in range(-2, 3)
    )
    b_sweeps = "\n".join(render_b_sweep(a) for a in range(-2, 3))
    predicate = """∀ (b : ℤ). -2 ≤ b → b < 3
          → ∀ (c : ℤ). -4 ≤ c → c < 5
          → 3 * (a * a) + 3 * (b * b) + c * c < 18
          → Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourTopShearNormalForm(
              Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate(a, b, c))"""
    facts = [
        (a, f"Matrix.rankFourDiagonalBranch_box_{fixed_name(a)}_all_b_c")
        for a in range(-2, 3)
    ]
    certificate = render_integer_all_from("P", predicate, "a", -2, 3, facts)
    final = f"""theorem Matrix.rankFourDiagonalBranch_finite_box_classified
        : ∀ (a : ℤ). -2 ≤ a → a < 3
          → ∀ (b : ℤ). -2 ≤ b → b < 3
          → ∀ (c : ℤ). -4 ≤ c → c < 5
          → 3 * (a * a) + 3 * (b * b) + c * c < 18
          → Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourTopShearNormalForm(
              Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate(a, b, c)) := {{
{certificate}
}}
"""
    return f"{c_sweeps}\n{b_sweeps}\n{final}"


def validate_search() -> list[tuple[int, int, int]]:
    borders = raw_borders()
    normal_forms = {
        (border[2] + 3 * reduce_border(border)[0][2], reduce_border(border)[1])
        for border in borders
    }
    assert len(normal_forms) == 18
    assert normal_forms == {(residue, corner) for residue in (-1, 0, 1) for corner in range(1, 7)}
    return borders


def render_certificates_module() -> str:
    borders = validate_search()
    certificates = "\n".join(render_certificate(border) for border in borders)
    return f"""-- Algebra/rank_four_diagonal_branch_generated.math
--
-- Generated by scripts/generate_rank_four_diagonal_branch.py.  Do not edit.
-- The untrusted search finds 109 raw borders and 18 balanced-residue top-shear
-- normal forms; every reduction below is checked by the kernel.

module Algebra.rank_four_diagonal_branch_generated

import Algebra.rank_four_diagonal_branch

{certificates}"""


def render_box_cases_module() -> str:
    validate_search()
    return f"""-- Algebra/rank_four_diagonal_branch_box_cases_generated.math
--
-- Generated by scripts/generate_rank_four_diagonal_branch.py.  Do not edit.
-- These 225 leaves turn the finite coordinate box into either one of the
-- 109 certified borders or an arithmetic contradiction.

module Algebra.rank_four_diagonal_branch_box_cases_generated

import Algebra.rank_four_diagonal_branch_generated

{render_box_cases()}"""


def render_classifier_module() -> str:
    validate_search()
    return f"""-- Algebra/rank_four_diagonal_branch_classification_generated.math
--
-- Generated by scripts/generate_rank_four_diagonal_branch.py.  Do not edit.
-- Explicit AllFrom certificates collect the 225 box leaves without search.

module Algebra.rank_four_diagonal_branch_classification_generated

import Algebra.rank_four_diagonal_branch_box_cases_generated

{render_box_classifier()}"""


def render(section: str) -> str:
    return {
        "certificates": render_certificates_module,
        "cases": render_box_cases_module,
        "classifier": render_classifier_module,
    }[section]()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--section", choices=OUTPUTS)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    if args.stdout:
        if args.section is None:
            parser.error("--stdout requires --section")
        sys.stdout.write(render(args.section))
        return 0
    sections = [args.section] if args.section is not None else list(OUTPUTS)
    if args.output is not None and len(sections) != 1:
        parser.error("--output requires --section")
    if args.check:
        for section in sections:
            output = args.output or OUTPUTS[section]
            if not output.exists() or output.read_text() != render(section):
                print(f"stale generated file: {output}", file=sys.stderr)
                return 1
        return 0
    for section in sections:
        output = args.output or OUTPUTS[section]
        output.write_text(render(section))
        print(f"wrote {output}")
    print("rank-four diagonal branch: 109 borders, 18 top-shear normal forms")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

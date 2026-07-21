#!/usr/bin/env python3
"""Generate finite rank-four classifiers above diag(1, 1, d).

The search performed here is deliberately untrusted.  For each configured
branch, the generated Math files certify every top-shear reduction and collect
the finite coordinate box with explicit ``Integer.AllFrom`` proofs.  Adding a
new diagonal branch should therefore be data entry in ``BRANCHES``, not a copy
of the proof renderer.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import itertools
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Branch:
    key: str
    module_stem: str
    description: str
    weight: int
    truant: int
    residue_start: int
    a_range: range
    b_range: range
    c_range: range
    expected_borders: int
    expected_normal_forms: int
    theorem_prefix: str
    source_module: str
    candidate: str
    representative: str
    normal_form_predicate: str
    reduction_theorem: str

    @property
    def bound(self) -> int:
        return self.weight * self.truant

    @property
    def outputs(self) -> dict[str, Path]:
        base = ROOT / "library/Algebra"
        return {
            "certificates": base / f"{self.module_stem}_generated.math",
            "cases": base / f"{self.module_stem}_box_cases_generated.math",
            "classifier": base / f"{self.module_stem}_classification_generated.math",
        }


BRANCHES = {
    "triple": Branch(
        key="triple",
        module_stem="rank_four_diagonal_branch",
        description="x^2 + y^2 + 3z^2",
        weight=3,
        truant=6,
        residue_start=-1,
        a_range=range(-2, 3),
        b_range=range(-2, 3),
        c_range=range(-4, 5),
        expected_borders=109,
        expected_normal_forms=18,
        theorem_prefix="rankFourDiagonalBranch",
        source_module="Algebra.rank_four_diagonal_branch",
        candidate="Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate",
        representative="Matrix.sumOfTwoSquaresPlusTripleSquareRankFourRepresentative",
        normal_form_predicate="Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourTopShearNormalForm",
        reduction_theorem="Matrix.sumOfTwoSquaresPlusTripleSquareRankFourCandidate_isometric_reduced",
    ),
    "double": Branch(
        key="double",
        module_stem="rank_four_double_diagonal_branch",
        description="x^2 + y^2 + 2z^2",
        weight=2,
        truant=14,
        residue_start=0,
        a_range=range(-3, 4),
        b_range=range(-3, 4),
        c_range=range(-5, 6),
        expected_borders=319,
        expected_normal_forms=25,
        theorem_prefix="rankFourDoubleDiagonalBranch",
        source_module="Algebra.rank_four_double_diagonal_branch",
        candidate="Matrix.sumOfTwoSquaresPlusDoubleSquareRankFourCandidate",
        representative="Matrix.sumOfTwoSquaresPlusDoubleSquareRankFourRepresentative",
        normal_form_predicate="Matrix.IsSumOfTwoSquaresPlusDoubleSquareRankFourTopShearNormalForm",
        reduction_theorem="Matrix.sumOfTwoSquaresPlusDoubleSquareRankFourCandidate_isometric_reduced",
    ),
}


def integer(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def name_coordinate(value: int) -> str:
    return f"m{-value}" if value < 0 else f"p{value}"


def weighted_expression(branch: Branch, a: str, b: str, c: str) -> str:
    return f"{branch.weight} * ({a} * {a}) + {branch.weight} * ({b} * {b}) + {c} * {c}"


def raw_borders(branch: Branch) -> list[tuple[int, int, int]]:
    borders = [
        border
        for border in itertools.product(branch.a_range, branch.b_range, branch.c_range)
        if branch.weight * border[0] ** 2 + branch.weight * border[1] ** 2 + border[2] ** 2
        < branch.bound
    ]
    assert len(borders) == branch.expected_borders
    return borders


def reduce_border(branch: Branch, border: tuple[int, int, int]) -> tuple[tuple[int, int, int], int, int]:
    a, b, c = border
    residue = (c - branch.residue_start) % branch.weight + branch.residue_start
    shift = (-a, -b, (residue - c) // branch.weight)
    x, y, z = shift
    corner = (
        branch.truant
        + 2 * (a * x + b * y + c * z)
        + x * x
        + y * y
        + branch.weight * z * z
    )
    return shift, residue, corner


def normal_forms(branch: Branch) -> list[tuple[int, int]]:
    forms = sorted({reduce_border(branch, border)[1:] for border in raw_borders(branch)})
    assert len(forms) == branch.expected_normal_forms
    return forms


def theorem_name(branch: Branch, border: tuple[int, int, int]) -> str:
    return "Matrix." + branch.theorem_prefix + "_border_" + "_".join(
        name_coordinate(value) for value in border
    )


def disjunction_introduction(index: int, count: int) -> str:
    if index == count - 1:
        return "Or.introduceRight(" * index + "reduced" + ")" * index
    return "Or.introduceRight(" * index + "Or.introduceLeft(reduced)" + ")" * index


def render_certificate(branch: Branch, border: tuple[int, int, int]) -> str:
    shift, residue_value, corner = reduce_border(branch, border)
    a, b, c = map(integer, border)
    x, y, z = map(integer, shift)
    az, bz, cz = (f"({value} : ℤ)" for value in (a, b, c))
    xz, yz, zz = (f"({value} : ℤ)" for value in (x, y, z))
    residue = integer(residue_value)
    index = normal_forms(branch).index((residue_value, corner))
    introduction = disjunction_introduction(index, branch.expected_normal_forms)
    return f"""automatic theorem {theorem_name(branch, border)}
        : {branch.normal_form_predicate}(
            {branch.candidate}({a}, {b}, {c})) := {{
  {az} + {xz} = 0 by ring as firstVanishes;
  {bz} + {yz} = 0 by ring as secondVanishes;
  {cz} + {branch.weight} * {zz} = ({residue} : ℤ) by ring as thirdReduces;
  ({branch.truant} : ℤ) + 2 * ({az} * {xz} + {bz} * {yz} + {cz} * {zz})
      + {xz} * {xz} + {yz} * {yz} + {branch.weight} * ({zz} * {zz}) = {corner} by ring as cornerReduces;
  Matrix.IsIsometric(
      {branch.candidate}({a}, {b}, {c}),
      {branch.representative}({residue}, {corner}))
      by {branch.reduction_theorem}(
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
    values: range,
    facts: list[tuple[int, str]],
) -> str:
    """Render an AllFrom certificate with every leaf cited explicitly."""
    start, stop = values.start, values.stop
    assert values.step == 1
    assert [value for value, _ in facts] == list(values)
    count = stop - start
    lines = [f"  let {predicate} : ℤ → Proposition := ({variable} : ℤ) ↦"]
    for index, line in enumerate(predicate_body.splitlines()):
        lines.append(("      " if index == 0 else "        ") + line)
    lines[-1] += ";"
    for value, proof in facts:
        lines.append(f"  {predicate}({integer(value)}) by {proof} as at_{fixed_name(value)};")
    lines.append(
        f"  Integer.AllFrom({predicate}, {integer(stop)}, 0) "
        f"by Integer.AllFrom.empty({predicate}, {integer(stop)}) as from_{fixed_name(stop)};"
    )
    for value in reversed(values):
        next_value = value + 1
        remaining = stop - next_value
        lines.append(
            f"  ({integer(next_value)} : ℤ) = ({integer(value)} : ℤ) + 1 by ring as step_{fixed_name(value)};"
        )
        lines.append(
            f"  Integer.AllFrom({predicate}, {integer(value)}, {1 + remaining}) by "
            f"Integer.AllFrom.prepend({predicate}, {integer(value)}, {integer(next_value)}, {remaining}, "
            f"step_{fixed_name(value)}, at_{fixed_name(value)}, from_{fixed_name(next_value)}) "
            f"as from_{fixed_name(value)};"
        )
    lines.append(f"  ({integer(stop)} : ℤ) = {integer(start)} + ({count} : ℤ) by ring as upperReads;")
    lines.append(f"  take {variable} : ℤ;")
    lines.append(f"  suppose {integer(start)} ≤ {variable} as lower;")
    lines.append(f"  suppose {variable} < {integer(stop)} as upper;")
    lines.append(
        f"  done by Integer.AllFrom_between({predicate}, {integer(start)}, {count}, {integer(stop)}, "
        f"upperReads, from_{fixed_name(start)}, {variable}, lower, upper)"
    )
    return "\n".join(lines)


def render_box_case(branch: Branch, a: int, b: int, c: int) -> str:
    name = f"Matrix.{branch.theorem_prefix}_box_case_{fixed_name(a)}_{fixed_name(b)}_{fixed_name(c)}"
    value = branch.weight * a * a + branch.weight * b * b + c * c
    expression = weighted_expression(branch, f"({a} : ℤ)", f"({b} : ℤ)", f"({c} : ℤ)")
    statement = f"""automatic theorem {name}
        (bound : {expression} < {branch.bound})
        : {branch.normal_form_predicate}(
            {branch.candidate}({a}, {b}, {c})) := {{
"""
    if value < branch.bound:
        body = f"  done by {theorem_name(branch, (a, b, c))}\n"
    else:
        body = f"""  {expression} = {value} by ring as valueReads;
  ({value} : ℤ) < {branch.bound} by substituting valueReads;
  ({branch.bound} : ℤ) ≤ {value};
  ({value} : ℤ) < {value};
  ({value} : ℕ) < {value} by Natural.to_integer.LessThan_reflects;
  False by Natural.lt_irreflexive;
  done
"""
    return statement + body + "}\n"


def render_c_sweep(branch: Branch, a: int, b: int) -> str:
    expression = weighted_expression(branch, f"({a} : ℤ)", f"({b} : ℤ)", "c")
    predicate = f"""{expression} < {branch.bound}
          → {branch.normal_form_predicate}(
              {branch.candidate}({a}, {b}, c))"""
    facts = [
        (c, f"Matrix.{branch.theorem_prefix}_box_case_{fixed_name(a)}_{fixed_name(b)}_{fixed_name(c)}")
        for c in branch.c_range
    ]
    certificate = render_integer_all_from("P", predicate, "c", branch.c_range, facts)
    return f"""automatic theorem Matrix.{branch.theorem_prefix}_box_{fixed_name(a)}_{fixed_name(b)}_all_c
        : ∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.normal_form_predicate}(
              {branch.candidate}({a}, {b}, c)) := {{
{certificate}
}}
"""


def render_b_sweep(branch: Branch, a: int) -> str:
    expression = weighted_expression(branch, f"({a} : ℤ)", "b", "c")
    predicate = f"""∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.normal_form_predicate}(
              {branch.candidate}({a}, b, c))"""
    facts = [
        (b, f"Matrix.{branch.theorem_prefix}_box_{fixed_name(a)}_{fixed_name(b)}_all_c")
        for b in branch.b_range
    ]
    certificate = render_integer_all_from("P", predicate, "b", branch.b_range, facts)
    return f"""automatic theorem Matrix.{branch.theorem_prefix}_box_{fixed_name(a)}_all_b_c
        : ∀ (b : ℤ). {branch.b_range.start} ≤ b → b < {branch.b_range.stop}
          → ∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.normal_form_predicate}(
              {branch.candidate}({a}, b, c)) := {{
{certificate}
}}
"""


def render_box_cases(branch: Branch) -> str:
    return "\n".join(
        render_box_case(branch, a, b, c)
        for a in branch.a_range
        for b in branch.b_range
        for c in branch.c_range
    )


def render_box_classifier(branch: Branch) -> str:
    c_sweeps = "\n".join(render_c_sweep(branch, a, b) for a in branch.a_range for b in branch.b_range)
    b_sweeps = "\n".join(render_b_sweep(branch, a) for a in branch.a_range)
    expression = weighted_expression(branch, "a", "b", "c")
    predicate = f"""∀ (b : ℤ). {branch.b_range.start} ≤ b → b < {branch.b_range.stop}
          → ∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.normal_form_predicate}(
              {branch.candidate}(a, b, c))"""
    facts = [
        (a, f"Matrix.{branch.theorem_prefix}_box_{fixed_name(a)}_all_b_c")
        for a in branch.a_range
    ]
    certificate = render_integer_all_from("P", predicate, "a", branch.a_range, facts)
    final = f"""theorem Matrix.{branch.theorem_prefix}_finite_box_classified
        : ∀ (a : ℤ). {branch.a_range.start} ≤ a → a < {branch.a_range.stop}
          → ∀ (b : ℤ). {branch.b_range.start} ≤ b → b < {branch.b_range.stop}
          → ∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.normal_form_predicate}(
              {branch.candidate}(a, b, c)) := {{
{certificate}
}}
"""
    return f"{c_sweeps}\n{b_sweeps}\n{final}"


def module_header(branch: Branch, section: str, detail: str) -> str:
    module = f"Algebra.{branch.module_stem}_{section}"
    imported = branch.source_module if section == "generated" else (
        f"Algebra.{branch.module_stem}_generated" if section == "box_cases_generated"
        else f"Algebra.{branch.module_stem}_box_cases_generated"
    )
    return f"""-- Algebra/{branch.module_stem}_{section}.math
--
-- Generated by scripts/generate_rank_four_diagonal_branch.py --branch {branch.key}.  Do not edit.
-- {detail}

module {module}

import {imported}

"""


def render(branch: Branch, section: str) -> str:
    forms = normal_forms(branch)
    if section == "certificates":
        detail = (
            f"The untrusted search finds {branch.expected_borders} raw borders and "
            f"{len(forms)} top-shear normal forms above {branch.description}; every reduction is kernel-checked."
        )
        return module_header(branch, "generated", detail) + "\n".join(
            render_certificate(branch, border) for border in raw_borders(branch)
        )
    if section == "cases":
        volume = len(branch.a_range) * len(branch.b_range) * len(branch.c_range)
        detail = f"These {volume} leaves turn the finite coordinate box into a certificate or an arithmetic contradiction."
        return module_header(branch, "box_cases_generated", detail) + render_box_cases(branch)
    if section == "classifier":
        detail = "Explicit AllFrom certificates collect the finite box leaves without proof search."
        return module_header(branch, "classification_generated", detail) + render_box_classifier(branch)
    raise ValueError(section)


def selected_branches(key: str | None) -> list[Branch]:
    return [BRANCHES[key]] if key is not None else list(BRANCHES.values())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", choices=BRANCHES)
    parser.add_argument("--section", choices=("certificates", "cases", "classifier"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    branches = selected_branches(args.branch)
    sections = [args.section] if args.section is not None else ["certificates", "cases", "classifier"]
    if (args.stdout or args.output is not None) and (len(branches) != 1 or len(sections) != 1):
        parser.error("--stdout/--output require one --branch and one --section")
    if args.stdout:
        sys.stdout.write(render(branches[0], sections[0]))
        return 0
    if args.check:
        for branch in branches:
            for section in sections:
                output = args.output or branch.outputs[section]
                if not output.exists() or output.read_text() != render(branch, section):
                    print(f"stale generated file: {output}", file=sys.stderr)
                    return 1
        return 0
    for branch in branches:
        for section in sections:
            output = args.output or branch.outputs[section]
            output.write_text(render(branch, section))
            print(f"wrote {output}")
        print(
            f"{branch.key}: {branch.expected_borders} borders, "
            f"{branch.expected_normal_forms} top-shear normal forms"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

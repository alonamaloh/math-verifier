#!/usr/bin/env python3
"""Generate the 207-way rank-four outcome dispatch.

Every selected rank-four normal form is either conditionally universal
(201 forms, each with its own cover theorem in the library) or one of the
six exceptional co-singleton forms (which represent every positive integer
except their truant).  This generator harvests the per-form theorems by
matching their `IsUniversal(<form>)` conclusions against the selected
normal-form chunk definitions, and emits one dispatch theorem per chunk,
per family, and the top-level `Matrix.selectedRankFourNormalForm_outcome`.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIB = ROOT / "projects/FifteenTheorem/Algebra"
OUTPUT = LIB / "rank_four_outcome_dispatch_generated.math"
SELECTED = LIB / "rank_four_selected_normal_forms_generated.math"

INTERFACE_VARIABLES = {
    "Matrix.ThreeSquaresConverse": "threeSquares",
    "Matrix.TripleSquaresConverse": "tripleSquares",
    "Matrix.OneTwoThreeConverse": "oneTwoThree",
    "Matrix.OneTwoFourConverse": "oneTwoFour",
    "Matrix.OneTwoSixConverse": "oneTwoSix",
    "Matrix.OneThreeSixLocalConverse": "oneThreeSix",
    "Integer.TwoThreeSixLocalConverse": "twoThreeSix",
    "Matrix.OneTwoFiveConverse": "oneTwoFive",
    "Matrix.DetSevenSafeConverse": "detSevenSafe",
}

# The interfaces the dispatch theorems take as parameters, in order.  The
# one-two-four and one-three-six interfaces are derived from three squares
# in the top-level theorem, so only seven roots reach the final statement.
PARAMETER_ORDER = [
    ("threeSquares", "Matrix.ThreeSquaresConverse"),
    ("tripleSquares", "Matrix.TripleSquaresConverse"),
    ("oneTwoThree", "Matrix.OneTwoThreeConverse"),
    ("oneTwoFour", "Matrix.OneTwoFourConverse"),
    ("oneTwoSix", "Matrix.OneTwoSixConverse"),
    ("oneThreeSix", "Matrix.OneThreeSixLocalConverse"),
    ("twoThreeSix", "Integer.TwoThreeSixLocalConverse"),
    ("oneTwoFive", "Matrix.OneTwoFiveConverse"),
    ("detSevenSafe", "Matrix.DetSevenSafeConverse"),
]

EXCEPTIONAL = {
    "Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, 0, 3)": (
        10, "Matrix.oddC4R0C3_representsEveryPositiveExceptTen", ["oneTwoSix"],
        "rank_four_exceptional_odd_c4_r0_c3", "Matrix.oddC4R0C3_truant_ten"),
    "Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, 2, 7)": (
        10, "Matrix.oddC4R2C7_representsEveryPositiveExceptTen", ["oneTwoFive"],
        "rank_four_exceptional_odd_c4_r2_c7_cover", "Matrix.oddC4R2C7_truant_ten"),
    "Matrix.squarePlusDoublePlusScaledRankFourRepresentative(5, 0, 0, 5)": (
        15, "Matrix.weightedD5S0R0C5_representsEveryPositiveExceptFifteen", ["oneTwoFive"],
        "rank_four_exceptional_weighted_d5_covers_generated",
        "Matrix.weightedD5S0R0C5_truant_fifteen"),
    "Matrix.squarePlusDoublePlusScaledRankFourRepresentative(5, 1, 1, 5)": (
        15, "Matrix.weightedD5S1R1C5_representsEveryPositiveExceptFifteen", ["oneTwoFive"],
        "rank_four_exceptional_weighted_d5_covers_generated",
        "Matrix.weightedD5S1R1C5_truant_fifteen"),
    "Matrix.squarePlusDoublePlusScaledRankFourRepresentative(5, 1, 1, 9)": (
        15, "Matrix.weightedD5S1R1C9_representsEveryPositiveExceptFifteen", ["oneTwoFive"],
        "rank_four_exceptional_weighted_d5_covers_generated",
        "Matrix.weightedD5S1R1C9_truant_fifteen"),
    "Matrix.squarePlusDoublePlusScaledRankFourRepresentative(5, 1, 2, 8)": (
        15, "Matrix.weightedD5S1R2C8_representsEveryPositiveExceptFifteen", ["oneTwoFive"],
        "rank_four_exceptional_weighted_d5_covers_generated",
        "Matrix.weightedD5S1R2C8_truant_fifteen"),
}


def normalize(expression: str) -> str:
    return " ".join(expression.split())


def harvest_universality():
    """Map each form expression to (theorem, [interface variables], module)."""
    table = {}
    for path in LIB.glob("*.math"):
        text = path.read_text()
        for match in re.finditer(
            r"theorem (Matrix\.\w+)\s*((?:\([^)]*\)|\s)*?)"
            r":\s*Matrix\.IsUniversal\(\s*([^)]*(?:\([^)]*\))?[^)]*)\)\s*:?=",
            text,
        ):
            name, parameters, argument = match.groups()
            interfaces = re.findall(
                r"\(\s*\w+\s*:\s*((?:Matrix|Integer)\.\w+Converse)\s*\)", parameters)
            occupied = re.findall(r"\(\s*[^:()]*:\s*", parameters)
            if not interfaces or len(occupied) != len(interfaces):
                continue
            variables = [INTERFACE_VARIABLES[i] for i in interfaces]
            table.setdefault(normalize(argument), []).append(
                (name, variables, path.stem))
    return table


def parse_selected():
    """Parse family/chunk structure of the selected normal forms."""
    text = SELECTED.read_text()
    blocks = re.split(r"\ndefinition ", text)
    definitions = {}
    order = []
    for block in blocks[1:]:
        name = block.split("\n")[0].split()[0]
        if not name.startswith("Matrix.IsSelectedRankFour"):
            continue
        body = block.split(":=", 1)[1]
        end = body.find("\ntheorem")
        if end >= 0:
            body = body[:end]
        forms = [normalize(f) for f in re.findall(r"R = (Matrix\.\w+\([^)]*\))", body)]
        children = re.findall(r"(Matrix\.IsSelectedRankFour\w+)\(R\)", body)
        definitions[name] = {"forms": forms, "children": children}
        order.append(name)
    return definitions, order


def parameters_block() -> str:
    return "".join(
        f"        ({variable} : {kind})\n" for variable, kind in PARAMETER_ORDER)


def arguments_list() -> str:
    return ", ".join(variable for variable, kind in PARAMETER_ORDER)


def case_arm(form: str, table) -> str:
    if form in EXCEPTIONAL:
        value, theorem, variables, module, truant_theorem = EXCEPTIONAL[form]
        side = ("Or.introduceRight(Or.introduceLeft(And.introduction(representedSet, isTruant)))"
                if value == 10 else
                "Or.introduceRight(Or.introduceRight(And.introduction(representedSet, isTruant)))")
        return f"""    case R = {form}: {{
        Matrix.RepresentsEveryPositiveExcept(
            {form}, {value})
            by {theorem}({", ".join(variables)}) as representedSet;
        Matrix.IsTruant({form}, {value})
            by {truant_theorem} as isTruant;
        done by {side}
      }}
"""
    candidates = table.get(form, [])
    assert len(candidates) == 1, (form, candidates)
    theorem, variables, module = candidates[0]
    return f"""    case R = {form}: {{
        Matrix.IsUniversal({form})
            by {theorem}({", ".join(variables)}) as universal;
        done by Or.introduceLeft(universal)
      }}
"""


def dispatch_theorem(kind: str, body: str) -> str:
    short = kind.split(".")[1]
    return f"""theorem Matrix.{short[0].lower()}{short[1:]}_outcome
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (selected : {kind}(R))
{parameters_block()}        : Matrix.IsUniversal(R)
          ∨ (Matrix.RepresentsEveryPositiveExcept(R, 10) ∧ Matrix.IsTruant(R, 10))
          ∨ (Matrix.RepresentsEveryPositiveExcept(R, 15) ∧ Matrix.IsTruant(R, 15)) := {body}
"""


def single_form_body(form: str, table) -> str:
    if form in EXCEPTIONAL:
        value, theorem, variables, module, truant_theorem = EXCEPTIONAL[form]
        side = ("Or.introduceRight(Or.introduceLeft(And.introduction(representedSet, isTruant)))"
                if value == 10 else
                "Or.introduceRight(Or.introduceRight(And.introduction(representedSet, isTruant)))")
        return f"""{{
  R = {form} by selected as reads;
  Matrix.RepresentsEveryPositiveExcept(
      {form}, {value})
      by {theorem}({", ".join(variables)});
  Matrix.RepresentsEveryPositiveExcept(R, {value})
      by substituting Equality.symmetry(reads) as representedSet;
  Matrix.IsTruant({form}, {value})
      by {truant_theorem};
  Matrix.IsTruant(R, {value}) by substituting Equality.symmetry(reads) as isTruant;
  done by {side}
}}"""
    candidates = table.get(form, [])
    assert len(candidates) == 1, (form, candidates)
    theorem, variables, module = candidates[0]
    return f"""{{
  R = {form} by selected as reads;
  Matrix.IsUniversal({form})
      by {theorem}({", ".join(variables)});
  Matrix.IsUniversal(R) by substituting Equality.symmetry(reads) as universal;
  done by Or.introduceLeft(universal)
}}"""


def single_child_body(child: str) -> str:
    short = child.split(".")[1]
    return f"""{{
  {child}(R) by selected as selectedChild;
  done by Matrix.{short[0].lower()}{short[1:]}_outcome(
    R, selectedChild, {arguments_list()})
}}"""


def render() -> str:
    table = harvest_universality()
    definitions, order = parse_selected()
    top = "Matrix.IsSelectedRankFourNormalForm"
    assert top in definitions

    modules = set()
    for name in order:
        for form in definitions[name]["forms"]:
            if form in EXCEPTIONAL:
                modules.add(EXCEPTIONAL[form][3]); modules.add("rank_four_exceptional_truants_generated")
            else:
                candidates = table.get(form, [])
                assert len(candidates) == 1, (form, candidates)
                modules.add(candidates[0][2])
    modules.add("one_two_four_converse_reduction")
    modules.add("one_three_six_converse_reduction")
    modules.add("exceptional_representation")
    modules.add("rank_four_selected_normal_forms_generated")
    imports = "\n".join(f"import Algebra.{module}" for module in sorted(modules))

    theorems = []
    for name in order:
        info = definitions[name]
        if name == top:
            continue
        if info["forms"]:
            if len(info["forms"]) == 1:
                theorems.append(dispatch_theorem(
                    name, single_form_body(info["forms"][0], table)))
            else:
                arms = "".join(case_arm(form, table) for form in info["forms"])
                theorems.append(dispatch_theorem(
                    name, f"\n  done by cases {{\n{arms}  }}"))
        else:
            if len(info["children"]) == 1:
                theorems.append(dispatch_theorem(
                    name, single_child_body(info["children"][0])))
            else:
                arms = ""
                for child in info["children"]:
                    short = child.split(".")[1]
                    arms += f"""    case {child}(R) as selectedChild:
      done by Matrix.{short[0].lower()}{short[1:]}_outcome(
        R, selectedChild, {arguments_list()})
"""
                theorems.append(dispatch_theorem(
                    name, f"\n  done by cases {{\n{arms}  }}"))

    # Top-level: cases over the nine family predicates, deriving the two
    # reduced interfaces from three squares.
    top_arms = ""
    for child in definitions[top]["children"]:
        short = child.split(".")[1]
        top_arms += f"""    case {child}(R) as selectedFamily: {{
        Matrix.IsUniversal(R)
          ∨ (Matrix.RepresentsEveryPositiveExcept(R, 10) ∧ Matrix.IsTruant(R, 10))
          ∨ (Matrix.RepresentsEveryPositiveExcept(R, 15) ∧ Matrix.IsTruant(R, 15))
            by Matrix.{short[0].lower()}{short[1:]}_outcome(
              R, selectedFamily, {arguments_list()});
        done
      }}
"""
    top_theorem = f"""theorem Matrix.selectedRankFourNormalForm_outcome
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (selected : Matrix.IsSelectedRankFourNormalForm(R))
        (threeSquares : Matrix.ThreeSquaresConverse)
        (tripleSquares : Matrix.TripleSquaresConverse)
        (oneTwoThree : Matrix.OneTwoThreeConverse)
        (oneTwoSix : Matrix.OneTwoSixConverse)
        (twoThreeSix : Integer.TwoThreeSixLocalConverse)
        (oneTwoFive : Matrix.OneTwoFiveConverse)
        (detSevenSafe : Matrix.DetSevenSafeConverse)
        : Matrix.IsUniversal(R)
          ∨ (Matrix.RepresentsEveryPositiveExcept(R, 10) ∧ Matrix.IsTruant(R, 10))
          ∨ (Matrix.RepresentsEveryPositiveExcept(R, 15) ∧ Matrix.IsTruant(R, 15)) := {{
  Matrix.OneTwoFourConverse
      by Matrix.one_two_four_converse_of_three_squares(threeSquares) as oneTwoFour;
  Matrix.OneThreeSixLocalConverse
      by Matrix.one_three_six_local_converse_of_three_squares(threeSquares) as oneThreeSix;
  done by cases {{
{top_arms}  }}
}}
"""
    theorems.append(top_theorem)

    return f"""-- Generated by scripts/generate_rank_four_outcome_dispatch.py.  Do not edit.
-- Every selected rank-four normal form is conditionally universal or one
-- of the six exceptional co-singleton forms.

module Algebra.rank_four_outcome_dispatch_generated

{imports}

{"".join(theorems)}"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    contents = render()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != contents:
            print(f"stale generated file: {OUTPUT}")
            return 1
        print("rank-four-outcome-dispatch-generated-check: PASS")
        return 0
    if not OUTPUT.exists() or OUTPUT.read_text() != contents:
        OUTPUT.write_text(contents)
        print(OUTPUT.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

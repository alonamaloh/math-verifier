#!/usr/bin/env python3
"""Generate the checked 207-representative rank-four classification surface."""

from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path
import re
import sys

from classify_rank_four_normal_forms import NamedForm, classify, named_forms
from generate_rank_four_isometry_certificates import form_expression, theorem_name


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "library/Algebra/rank_four_global_classification_generated.math"
DEFINITIONS_OUTPUT = ROOT / "library/Algebra/rank_four_selected_normal_forms_generated.math"
BRANCH_OUTPUT = ROOT / "library/Algebra/rank_four_global_branch_coverage_generated.math"
CHUNK_SIZE = 8

FAMILIES = (
    "pilot",
    "triple",
    "double",
    "weighted.d2",
    "weighted.d3",
    "weighted.d4",
    "weighted.d5",
    "odd.c4",
    "odd.c5",
)

FAMILY_DEFINITIONS = {
    "pilot": "Matrix.IsSelectedRankFourPilotNormalForm",
    "triple": "Matrix.IsSelectedRankFourTripleNormalForm",
    "double": "Matrix.IsSelectedRankFourDoubleNormalForm",
    "weighted.d2": "Matrix.IsSelectedRankFourWeightedD2NormalForm",
    "weighted.d3": "Matrix.IsSelectedRankFourWeightedD3NormalForm",
    "weighted.d4": "Matrix.IsSelectedRankFourWeightedD4NormalForm",
    "weighted.d5": "Matrix.IsSelectedRankFourWeightedD5NormalForm",
    "odd.c4": "Matrix.IsSelectedRankFourOddC4NormalForm",
    "odd.c5": "Matrix.IsSelectedRankFourOddC5NormalForm",
}

BRANCHES = {
    "pilot": (
        "Matrix.IsSumOfThreeSquaresRankFourPilotRepresentative",
        "Matrix.sumOfThreeSquaresRankFourPilotRepresentative_is_global",
    ),
    "triple": (
        "Matrix.IsSumOfTwoSquaresPlusTripleSquareRankFourSignedNormalForm",
        "Matrix.sumOfTwoSquaresPlusTripleSquareRankFourNormalForm_is_global",
    ),
    "double": (
        "Matrix.IsSumOfTwoSquaresPlusDoubleSquareRankFourTopShearNormalForm",
        "Matrix.sumOfTwoSquaresPlusDoubleSquareRankFourNormalForm_is_global",
    ),
    "weighted.d2": (
        "Matrix.IsRankFourWeightedDiagonalD2NormalForm",
        "Matrix.rankFourWeightedDiagonalD2NormalForm_is_global",
    ),
    "weighted.d3": (
        "Matrix.IsRankFourWeightedDiagonalD3NormalForm",
        "Matrix.rankFourWeightedDiagonalD3NormalForm_is_global",
    ),
    "weighted.d4": (
        "Matrix.IsRankFourWeightedDiagonalD4NormalForm",
        "Matrix.rankFourWeightedDiagonalD4NormalForm_is_global",
    ),
    "weighted.d5": (
        "Matrix.IsRankFourWeightedDiagonalD5NormalForm",
        "Matrix.rankFourWeightedDiagonalD5NormalForm_is_global",
    ),
    "odd.c4": (
        "Matrix.IsRankFourOddDiagonalC4NormalForm",
        "Matrix.rankFourOddDiagonalC4NormalForm_is_global",
    ),
    "odd.c5": (
        "Matrix.IsRankFourOddDiagonalC5NormalForm",
        "Matrix.rankFourOddDiagonalC5NormalForm_is_global",
    ),
}

BRANCH_IMPORTS = {
    "pilot": "Algebra.rank_four_pilot",
    "triple": "Algebra.rank_four_diagonal_branch_coverage",
    "double": "Algebra.rank_four_double_diagonal_branch_coverage",
    "weighted.d2": "Algebra.rank_four_weighted_diagonal_branches_coverage",
    "weighted.d3": "Algebra.rank_four_weighted_diagonal_branches_coverage",
    "weighted.d4": "Algebra.rank_four_weighted_diagonal_branches_coverage",
    "weighted.d5": "Algebra.rank_four_weighted_diagonal_branches_coverage",
    "odd.c4": "Algebra.rank_four_odd_diagonal_branches_coverage",
    "odd.c5": "Algebra.rank_four_odd_diagonal_branches_coverage",
}


def safe_name(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", name).strip("_")


def or_expression(expressions: list[str], indent: str = "  ") -> str:
    assert expressions
    return (f"\n{indent}∨ ").join(expressions)


def or_intro(index: int, count: int, value: str) -> str:
    assert 0 <= index < count
    return value if count == 1 else f"disjunct({value})"


def promotion_name(form: NamedForm) -> str:
    return f"Matrix.rankFourGlobalRepresentative_{safe_name(form.name)}"


def render_family_definition(family: str, representatives: list[NamedForm]) -> str:
    chunks = [representatives[index:index + CHUNK_SIZE] for index in range(0, len(representatives), CHUNK_SIZE)]
    chunk_definitions = []
    for index, chunk in enumerate(chunks):
        expressions = [f"R = {form_expression(form)}" for form in chunk]
        chunk_definitions.append(f"""definition {FAMILY_DEFINITIONS[family]}Chunk{index}
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4)) : Proposition :=
  {or_expression(expressions, '  ')}
""")
    family_expression = or_expression(
        [f"{FAMILY_DEFINITIONS[family]}Chunk{index}(R)" for index in range(len(chunks))],
        "  ",
    )
    return "\n".join(chunk_definitions) + f"""
definition {FAMILY_DEFINITIONS[family]}
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4)) : Proposition :=
  {family_expression}
"""


def render_promotion(
    form: NamedForm,
    chosen: NamedForm,
    family_representatives: dict[str, list[NamedForm]],
    identification_by_source,
) -> str:
    family = chosen.family
    within = family_representatives[family]
    selected_index = within.index(chosen)
    chunk_index = selected_index // CHUNK_SIZE
    index_within_chunk = selected_index % CHUNK_SIZE
    chunk_count = (len(within) + CHUNK_SIZE - 1) // CHUNK_SIZE
    selected_chunk = within[chunk_index * CHUNK_SIZE:(chunk_index + 1) * CHUNK_SIZE]
    family_index = FAMILIES.index(family)
    equality_proof = or_intro(index_within_chunk, len(selected_chunk), "chosenReads")
    chunk_proof = or_intro(chunk_index, chunk_count, "withinChunk")
    global_proof = or_intro(family_index, len(FAMILIES), "withinFamily")
    if form.name == chosen.name:
        canonical = "Matrix.IsIsometric(B, chosen) by isometric as canonical;"
    else:
        identification = identification_by_source[form.name]
        canonical = f"""Matrix.IsIsometric(B, chosen) by Matrix.IsIsometric.transitive(
      leftIsometric := isometric,
      rightIsometric := {theorem_name(identification)}) as canonical;"""
    return f"""theorem {promotion_name(form)}
        (B : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (isometric : Matrix.IsIsometric(B, {form_expression(form)}))
        : Matrix.IsRankFourEscalatorRepresentative(B) := {{
  let chosen : Matrix(Integer.commutative_ring_bundle, 4, 4) := {form_expression(chosen)};
  {canonical}
  chosen = chosen by reflexivity(Matrix(Integer.commutative_ring_bundle, 4, 4), chosen) as chosenReads;
  {FAMILY_DEFINITIONS[family]}Chunk{chunk_index}(chosen) by {equality_proof} as withinChunk;
  {FAMILY_DEFINITIONS[family]}(chosen) by {chunk_proof} as withinFamily;
  Matrix.IsSelectedRankFourNormalForm(chosen) by {global_proof} as selected;
  witness chosen with done by And.introduction(selected, canonical)
}}
"""


def case_tree(forms: list[NamedForm], indent: str = "  ") -> str:
    assert len(forms) >= 2
    cases = "\n".join(
        f"{indent}  case Matrix.IsIsometric(B, {form_expression(form)}) as isometric: "
        f"done by {promotion_name(form)}(isometric := isometric)"
        for form in forms
    )
    return f"""{indent}done by cases {{
{cases}
{indent}}}"""


def render_branch(family: str, forms: list[NamedForm]) -> str:
    predicate, theorem = BRANCHES[family]
    return f"""theorem {theorem}
        (B : Matrix(Integer.commutative_ring_bundle, 4, 4))
        (classified : {predicate}(B))
        : Matrix.IsRankFourEscalatorRepresentative(B) := {{
{case_tree(forms)}
}}
"""


def classification_data():
    forms = named_forms()
    representatives, identifications = classify(forms, theta_limit=15)
    assert len(forms) == 276
    assert len(representatives) == 207
    assert len(identifications) == 69

    representatives_by_family: dict[str, list[NamedForm]] = defaultdict(list)
    for representative in representatives:
        representatives_by_family[representative.family].append(representative)
    assert tuple(representatives_by_family) == FAMILIES

    representative_by_name = {form.name: form for form in representatives}
    identification_by_source = {item.source.name: item for item in identifications}
    chosen_by_source = {
        form.name: representative_by_name.get(form.name, identification_by_source[form.name].representative)
        if form.name not in representative_by_name
        else representative_by_name[form.name]
        for form in forms
    }

    family_definitions = "\n".join(
        render_family_definition(family, representatives_by_family[family])
        for family in FAMILIES
    )
    selected_families = [f"{FAMILY_DEFINITIONS[family]}(R)" for family in FAMILIES]
    promotions = "\n".join(
        render_promotion(
            form,
            chosen_by_source[form.name],
            representatives_by_family,
            identification_by_source,
        )
        for form in forms
    )
    grouped_forms: dict[str, list[NamedForm]] = defaultdict(list)
    for form in forms:
        grouped_forms[form.family].append(form)
    return forms, family_definitions, selected_families, promotions, grouped_forms


def render_definitions(data) -> str:
    _, family_definitions, selected_families, _, _ = data
    return f"""-- Algebra/rank_four_selected_normal_forms_generated.math
-- Generated by scripts/generate_rank_four_global_classification.py.  Do not edit.
-- The chunked predicates name exactly 207 selected concrete matrices while
-- keeping every proof term shallow enough for predictable elaboration.

module Algebra.rank_four_selected_normal_forms_generated

import Algebra.rank_four_isometry_certificates

{family_definitions}
definition Matrix.IsSelectedRankFourNormalForm
        (R : Matrix(Integer.commutative_ring_bundle, 4, 4)) : Proposition :=
  {or_expression(selected_families, '  ')}

definition Matrix.IsRankFourEscalatorRepresentative
        (B : Matrix(Integer.commutative_ring_bundle, 4, 4)) : Proposition :=
  ∃ (R : Matrix(Integer.commutative_ring_bundle, 4, 4)).
      Matrix.IsSelectedRankFourNormalForm(R) ∧ Matrix.IsIsometric(B, R)
"""


def render_core(data) -> str:
    _, _, _, promotions, _ = data
    return f"""-- Algebra/rank_four_global_classification_generated.math
-- Generated by scripts/generate_rank_four_global_classification.py.  Do not edit.
-- The 69 nontrivial identifications invoked below are explicit kernel-checked
-- certificates; this file merges the old 276-way branch cover into 207 names.

module Algebra.rank_four_global_classification_generated

import Algebra.rank_four_isometry_certificates_generated
import Algebra.rank_four_selected_normal_forms_generated

{promotions}
"""


def render_branch_module(grouped_forms: dict[str, list[NamedForm]]) -> str:
    imports = "\n".join(f"import {module}" for module in dict.fromkeys(BRANCH_IMPORTS.values()))
    branches = "\n".join(render_branch(family, grouped_forms[family]) for family in FAMILIES)
    return f"""-- Algebra/rank_four_global_branch_coverage_generated.math
-- Generated by scripts/generate_rank_four_global_classification.py.  Do not edit.

module Algebra.rank_four_global_branch_coverage_generated

import Algebra.rank_four_global_classification_generated
{imports}

{branches}"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    data = classification_data()
    generated = render_core(data)
    definitions_generated = render_definitions(data)
    grouped_forms = data[-1]
    branch_generated = render_branch_module(grouped_forms)
    if args.stdout:
        sys.stdout.write(generated)
        return 0
    if args.check:
        if not args.output.exists() or args.output.read_text() != generated:
            print(f"stale generated file: {args.output}", file=sys.stderr)
            return 1
        if not DEFINITIONS_OUTPUT.exists() or DEFINITIONS_OUTPUT.read_text() != definitions_generated:
            print(f"stale generated file: {DEFINITIONS_OUTPUT}", file=sys.stderr)
            return 1
        if not BRANCH_OUTPUT.exists() or BRANCH_OUTPUT.read_text() != branch_generated:
            print(f"stale generated file: {BRANCH_OUTPUT}", file=sys.stderr)
            return 1
        return 0
    args.output.write_text(generated)
    DEFINITIONS_OUTPUT.write_text(definitions_generated)
    BRANCH_OUTPUT.write_text(branch_generated)
    print(f"wrote three generated classification modules: 276 branch forms collapsed to 207 representatives")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

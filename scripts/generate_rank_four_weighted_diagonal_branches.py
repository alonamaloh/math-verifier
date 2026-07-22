#!/usr/bin/env python3
"""Generate finite classifiers for the five diag(1, 2, d) rank-four branches.

The search is untrusted.  Generated declarations certify every shear and
collect every point of a formally proved coordinate box.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import itertools
from pathlib import Path
import sys

from generate_rank_four_diagonal_branch import (
    BRANCHES as DIAGONAL_BRANCHES,
    integer,
    name_coordinate,
    normal_forms as diagonal_normal_forms,
    render_integer_all_from,
)


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Branch:
    d: int
    truant: int
    a_range: range
    b_range: range
    c_range: range
    expected_borders: int
    expected_normal_forms: int
    certificate_chunk_size: int | None = None
    box_case_chunk_size: int | None = None
    classification_chunk_size: int | None = None

    @property
    def key(self) -> str:
        return f"d{self.d}"

    @property
    def stem(self) -> str:
        return f"rank_four_weighted_diagonal_{self.key}"

    @property
    def theorem_prefix(self) -> str:
        return f"rankFourWeightedDiagonalD{self.d}"

    @property
    def predicate(self) -> str:
        return f"Matrix.IsRankFourWeightedDiagonalD{self.d}NormalForm"

    @property
    def bound(self) -> int:
        return 2 * self.d * self.truant

    @property
    def outputs(self) -> dict[str, Path]:
        base = ROOT / "library/Algebra"
        return {
            section: base / f"{self.stem}_{suffix}.math"
            for section, suffix in (
                ("normal_forms", "normal_forms_generated"),
                ("certificates", "generated"),
                ("cases", "box_cases_generated"),
                ("classifier", "classification_generated"),
            )
        }


BRANCHES = {
    branch.key: branch
    for branch in (
        Branch(1, 14, range(-3, 4), range(-5, 6), range(-3, 4), 319, 25),
        Branch(2, 7, range(-2, 3), range(-3, 4), range(-3, 4), 161, 18),
        Branch(3, 10, range(-3, 4), range(-5, 6), range(-5, 6), 341, 36),
        Branch(
            4,
            14,
            range(-3, 4),
            range(-5, 6),
            range(-7, 8),
            631,
            68,
            certificate_chunk_size=20,
            box_case_chunk_size=20,
            classification_chunk_size=20,
        ),
        Branch(5, 10, range(-3, 4), range(-5, 6), range(-7, 8), 425, 52),
    )
}


def fixed_name(value: int) -> str:
    return name_coordinate(value)


def candidate(branch: Branch, a: str, b: str, c: str) -> str:
    return (
        "Matrix.squarePlusDoublePlusScaledRankFourCandidate"
        f"({branch.d}, {branch.truant}, {a}, {b}, {c})"
    )


def representative(branch: Branch, second: int, third: int, corner: int) -> str:
    return (
        "Matrix.squarePlusDoublePlusScaledRankFourRepresentative"
        f"({branch.d}, {integer(second)}, {integer(third)}, {corner})"
    )


def orbit_representative(branch: Branch, form: tuple[int, int, int]) -> str:
    second, third, corner = form
    if branch.d == 1:
        assert third == 0
        return f"Matrix.sumOfTwoSquaresPlusDoubleSquareRankFourRepresentative({integer(second)}, {corner})"
    return representative(branch, second, third, corner)


def bound_expression(branch: Branch, a: str, b: str, c: str) -> str:
    return (
        f"{2 * branch.d} * ({a} * {a}) + {branch.d} * ({b} * {b}) "
        f"+ 2 * ({c} * {c})"
    )


def raw_borders(branch: Branch) -> list[tuple[int, int, int]]:
    borders = [
        border
        for border in itertools.product(branch.a_range, branch.b_range, branch.c_range)
        if 2 * branch.d * border[0] ** 2
        + branch.d * border[1] ** 2
        + 2 * border[2] ** 2
        < branch.bound
    ]
    assert len(borders) == branch.expected_borders
    return borders


def reduce_border(
    branch: Branch, border: tuple[int, int, int]
) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    a, b, c = border
    second = b % 2
    third = c % branch.d
    shift = (-a, (second - b) // 2, (third - c) // branch.d)
    x, y, z = shift
    corner = (
        branch.truant
        + 2 * (a * x + b * y + c * z)
        + x * x
        + 2 * y * y
        + branch.d * z * z
    )
    return shift, (second, third, corner)


def reflect_form(
    branch: Branch, form: tuple[int, int, int]
) -> tuple[tuple[int, int, int], int]:
    """Reflect the d-weighted coordinate and return it to [0,d)."""
    second, third, corner = form
    reflected_third = (-third) % branch.d
    shift = (reflected_third + third) // branch.d
    reflected_corner = corner + 2 * (-third) * shift + branch.d * shift * shift
    return (second, reflected_third, reflected_corner), shift


def canonical_form(branch: Branch, form: tuple[int, int, int]) -> tuple[int, int, int]:
    reflected, _ = reflect_form(branch, form)
    orbit = {form, reflected}
    if branch.d == 2:
        orbit.update((third, second, corner) for second, third, corner in tuple(orbit))
    return min(orbit)


def normal_forms(branch: Branch) -> list[tuple[int, int, int]]:
    forms = sorted(
        {
            canonical_form(branch, reduce_border(branch, border)[1])
            for border in raw_borders(branch)
        }
    )
    assert len(forms) == branch.expected_normal_forms
    return forms


def border_theorem(branch: Branch, border: tuple[int, int, int]) -> str:
    return "Matrix." + branch.theorem_prefix + "_border_" + "_".join(
        fixed_name(value) for value in border
    )


def render_normal_forms(branch: Branch) -> str:
    if branch.d == 1:
        forms = [(second, corner) for second, third, corner in normal_forms(branch)]
        assert all(third == 0 for _, third, _ in normal_forms(branch))
        assert forms == diagonal_normal_forms(DIAGONAL_BRANCHES["double"])
        body = "Matrix.IsSumOfTwoSquaresPlusDoubleSquareRankFourTopShearNormalForm(B)"
    else:
        clauses = [
            f"Matrix.IsIsometric(B, {orbit_representative(branch, form)})"
            for form in normal_forms(branch)
        ]
        body = "\n    ∨ ".join(clauses)
    return f"""-- Algebra/{branch.stem}_normal_forms_generated.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.

module Algebra.{branch.stem}_normal_forms_generated

import Algebra.rank_four_weighted_diagonal_orbits

definition {branch.predicate}
        (B : Matrix(Integer.commutative_ring_bundle, 4, 4)) : Proposition :=
  {body}
"""


def render_certificate(branch: Branch, border: tuple[int, int, int]) -> str:
    shift, reduced_form = reduce_border(branch, border)
    second, third, corner = reduced_form
    form = canonical_form(branch, reduced_form)
    canonical_second, canonical_third, canonical_corner = form
    a, b, c = map(integer, border)
    x, y, z = map(integer, shift)
    az, bz, cz = (f"({value} : ℤ)" for value in (a, b, c))
    xz, yz, zz = (f"({value} : ℤ)" for value in (x, y, z))
    assert form in normal_forms(branch)
    proof_name = "reduced" if form == reduced_form and branch.d != 1 else "canonicalized"
    introduction = f"disjunct({proof_name})"
    canonical_proof = ""
    if branch.d == 1:
        canonical_proof = f"""  Matrix.IsIsometric(
      {representative(branch, second, third, corner)},
      {orbit_representative(branch, form)})
      by Matrix.squarePlusDoublePlusScaledRankFourRepresentative_one_isometric_double_diagonal
  as orbitReduction;
  Matrix.IsIsometric(
      {candidate(branch, a, b, c)},
      {orbit_representative(branch, form)})
      by Matrix.IsIsometric.transitive(leftIsometric := reduced, rightIsometric := orbitReduction)
  as canonicalized;
"""
    elif form != reduced_form:
        swapped = (third, second, corner)
        if branch.d == 2 and swapped == form:
            canonical_proof = f"""  Matrix.IsIsometric(
      {representative(branch, second, third, corner)},
      {representative(branch, canonical_second, canonical_third, canonical_corner)})
      by Matrix.squarePlusDoublePlusScaledRankFourRepresentative_two_isometric_swap_residues
  as orbitReduction;
  Matrix.IsIsometric(
      {candidate(branch, a, b, c)},
      {representative(branch, canonical_second, canonical_third, canonical_corner)})
      by Matrix.IsIsometric.transitive(leftIsometric := reduced, rightIsometric := orbitReduction)
  as canonicalized;
"""
        else:
            reflected, reflection_shift = reflect_form(branch, reduced_form)
            assert reflected == form
            canonical_proof = f"""  -({third} : ℤ) + {branch.d} * ({reflection_shift} : ℤ) = ({canonical_third} : ℤ) by ring as thirdReflects;
  ({corner} : ℤ) + 2 * (-({third} : ℤ) * ({reflection_shift} : ℤ))
      + {branch.d} * (({reflection_shift} : ℤ) * ({reflection_shift} : ℤ)) = {canonical_corner}
      by ring as cornerReflects;
  Matrix.IsIsometric(
      {representative(branch, second, third, corner)},
      {representative(branch, canonical_second, canonical_third, canonical_corner)})
      by Matrix.squarePlusDoublePlusScaledRankFourRepresentative_isometric_reflected(
        z := {reflection_shift}, reflectedThird := {canonical_third}, reflectedCorner := {canonical_corner},
        thirdMoves := thirdReflects, cornerMoves := cornerReflects)
  as orbitReduction;
  Matrix.IsIsometric(
      {candidate(branch, a, b, c)},
      {representative(branch, canonical_second, canonical_third, canonical_corner)})
      by Matrix.IsIsometric.transitive(leftIsometric := reduced, rightIsometric := orbitReduction)
  as canonicalized;
"""
    return f"""theorem {border_theorem(branch, border)}
        : {branch.predicate}({candidate(branch, a, b, c)}) := {{
  {az} + {xz} = 0 by ring as firstVanishes;
  {bz} + 2 * {yz} = ({second} : ℤ) by ring as secondReduces;
  {cz} + {branch.d} * {zz} = ({third} : ℤ) by ring as thirdReduces;
  ({branch.truant} : ℤ) + 2 * ({az} * {xz} + {bz} * {yz} + {cz} * {zz})
      + {xz} * {xz} + 2 * ({yz} * {yz}) + {branch.d} * ({zz} * {zz}) = {corner} by ring as cornerReduces;
  Matrix.IsIsometric(
      {candidate(branch, a, b, c)},
      {representative(branch, second, third, corner)})
      by Matrix.squarePlusDoublePlusScaledRankFourCandidate_isometric_reduced(
        x := {x}, y := {y}, z := {z}, secondResidue := {second}, thirdResidue := {third}, corner := {corner},
        firstVanishes := firstVanishes, secondReduces := secondReduces,
        thirdReduces := thirdReduces, cornerReduces := cornerReduces)
  as reduced;
{canonical_proof}  done by {introduction}
}}
"""


def render_certificates(branch: Branch) -> str:
    certificates = "\n".join(render_certificate(branch, border) for border in raw_borders(branch))
    return f"""-- Algebra/{branch.stem}_generated.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.
-- {branch.expected_borders} admissible borders reduce to {branch.expected_normal_forms} parent-automorphism forms.

module Algebra.{branch.stem}_generated

import Algebra.{branch.stem}_normal_forms_generated

{certificates}"""


def certificate_chunks(branch: Branch) -> list[list[tuple[int, int, int]]]:
    borders = raw_borders(branch)
    if branch.certificate_chunk_size is None:
        return [borders]
    size = branch.certificate_chunk_size
    assert size > 0
    return [borders[start : start + size] for start in range(0, len(borders), size)]


def certificate_chunk_stem(branch: Branch, index: int) -> str:
    return f"{branch.stem}_certificates_{index + 1:02d}_generated"


def render_certificate_chunk(
    branch: Branch, index: int, borders: list[tuple[int, int, int]], chunk_count: int
) -> str:
    stem = certificate_chunk_stem(branch, index)
    certificates = "\n".join(render_certificate(branch, border) for border in borders)
    return f"""-- Algebra/{stem}.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.
-- Certificate chunk {index + 1} of {chunk_count}: {len(borders)} admissible borders.

module Algebra.{stem}

import Algebra.{branch.stem}_normal_forms_generated

{certificates}"""


def render_certificate_aggregate(branch: Branch, chunk_count: int) -> str:
    imports = "\n".join(
        f"import Algebra.{certificate_chunk_stem(branch, index)}"
        for index in range(chunk_count)
    )
    return f"""-- Algebra/{branch.stem}_generated.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.
-- {branch.expected_borders} admissible borders reduce to {branch.expected_normal_forms} parent-automorphism forms.
-- The certificates are split into {chunk_count} bounded-size modules to avoid quadratic same-module elaboration cost.

module Algebra.{branch.stem}_generated

{imports}
"""


def render_box_case(branch: Branch, a: int, b: int, c: int) -> str:
    name = f"Matrix.{branch.theorem_prefix}_box_case_{fixed_name(a)}_{fixed_name(b)}_{fixed_name(c)}"
    expression = bound_expression(branch, f"({a} : ℤ)", f"({b} : ℤ)", f"({c} : ℤ)")
    value = 2 * branch.d * a * a + branch.d * b * b + 2 * c * c
    if value < branch.bound:
        proof = f"  done by {border_theorem(branch, (a, b, c))}\n"
    else:
        proof = f"""  {expression} = {value} by ring as valueReads;
  ({value} : ℤ) < {branch.bound} by substituting valueReads;
  ({branch.bound} : ℤ) ≤ {value};
  ({value} : ℤ) < {value};
  ({value} : ℕ) < {value} by Natural.to_integer.LessThan_reflects;
  False by Natural.lt_irreflexive;
  done
"""
    return f"""theorem {name}
        (bound : {expression} < {branch.bound})
        : {branch.predicate}({candidate(branch, str(a), str(b), str(c))}) := {{
{proof}}}
"""


def render_cases(branch: Branch) -> str:
    cases = box_cases(branch)
    leaves = "\n".join(render_box_case(branch, a, b, c) for a, b, c in cases)
    return f"""-- Algebra/{branch.stem}_box_cases_generated.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.
-- {len(cases)} explicit finite-box leaves.

module Algebra.{branch.stem}_box_cases_generated

import Algebra.{branch.stem}_generated

{leaves}"""


def box_cases(branch: Branch) -> list[tuple[int, int, int]]:
    return list(itertools.product(branch.a_range, branch.b_range, branch.c_range))


def box_case_chunks(branch: Branch) -> list[list[tuple[int, int, int]]]:
    cases = box_cases(branch)
    if branch.box_case_chunk_size is None:
        return [cases]
    size = branch.box_case_chunk_size
    assert size > 0
    return [cases[start : start + size] for start in range(0, len(cases), size)]


def box_case_chunk_stem(branch: Branch, index: int) -> str:
    return f"{branch.stem}_box_cases_{index + 1:02d}_generated"


def render_box_case_chunk(
    branch: Branch, index: int, cases: list[tuple[int, int, int]], chunk_count: int
) -> str:
    stem = box_case_chunk_stem(branch, index)
    leaves = "\n".join(render_box_case(branch, a, b, c) for a, b, c in cases)
    return f"""-- Algebra/{stem}.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.
-- Box-case chunk {index + 1} of {chunk_count}: {len(cases)} explicit finite-box leaves.

module Algebra.{stem}

import Algebra.{branch.stem}_generated

{leaves}"""


def render_box_case_aggregate(branch: Branch, chunk_count: int) -> str:
    imports = "\n".join(
        f"import Algebra.{box_case_chunk_stem(branch, index)}"
        for index in range(chunk_count)
    )
    return f"""-- Algebra/{branch.stem}_box_cases_generated.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.
-- {len(box_cases(branch))} explicit finite-box leaves.
-- The leaves are split into {chunk_count} bounded-size modules to avoid quadratic same-module elaboration cost.

module Algebra.{branch.stem}_box_cases_generated

{imports}
"""


def render_c_sweep(branch: Branch, a: int, b: int) -> str:
    expression = bound_expression(branch, f"({a} : ℤ)", f"({b} : ℤ)", "c")
    predicate = f"""{expression} < {branch.bound}
          → {branch.predicate}({candidate(branch, str(a), str(b), 'c')})"""
    facts = [
        (c, f"Matrix.{branch.theorem_prefix}_box_case_{fixed_name(a)}_{fixed_name(b)}_{fixed_name(c)}")
        for c in branch.c_range
    ]
    certificate = render_integer_all_from("P", predicate, "c", branch.c_range, facts)
    return f"""theorem Matrix.{branch.theorem_prefix}_box_{fixed_name(a)}_{fixed_name(b)}_all_c
        : ∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.predicate}({candidate(branch, str(a), str(b), 'c')}) := {{
{certificate}
}}
"""


def render_b_sweep(branch: Branch, a: int) -> str:
    expression = bound_expression(branch, f"({a} : ℤ)", "b", "c")
    predicate = f"""∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.predicate}({candidate(branch, str(a), 'b', 'c')})"""
    facts = [
        (b, f"Matrix.{branch.theorem_prefix}_box_{fixed_name(a)}_{fixed_name(b)}_all_c")
        for b in branch.b_range
    ]
    certificate = render_integer_all_from("P", predicate, "b", branch.b_range, facts)
    return f"""theorem Matrix.{branch.theorem_prefix}_box_{fixed_name(a)}_all_b_c
        : ∀ (b : ℤ). {branch.b_range.start} ≤ b → b < {branch.b_range.stop}
          → ∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.predicate}({candidate(branch, str(a), 'b', 'c')}) := {{
{certificate}
}}
"""


def render_classifier_final(branch: Branch) -> str:
    expression = bound_expression(branch, "a", "b", "c")
    predicate = f"""∀ (b : ℤ). {branch.b_range.start} ≤ b → b < {branch.b_range.stop}
          → ∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.predicate}({candidate(branch, 'a', 'b', 'c')})"""
    facts = [
        (a, f"Matrix.{branch.theorem_prefix}_box_{fixed_name(a)}_all_b_c")
        for a in branch.a_range
    ]
    certificate = render_integer_all_from("P", predicate, "a", branch.a_range, facts)
    return f"""theorem Matrix.{branch.theorem_prefix}_finite_box_classified
        : ∀ (a : ℤ). {branch.a_range.start} ≤ a → a < {branch.a_range.stop}
          → ∀ (b : ℤ). {branch.b_range.start} ≤ b → b < {branch.b_range.stop}
          → ∀ (c : ℤ). {branch.c_range.start} ≤ c → c < {branch.c_range.stop}
          → {expression} < {branch.bound}
          → {branch.predicate}({candidate(branch, 'a', 'b', 'c')}) := {{
{certificate}
}}
"""


def render_classifier(branch: Branch) -> str:
    c_sweeps = "\n".join(render_c_sweep(branch, a, b) for a in branch.a_range for b in branch.b_range)
    b_sweeps = "\n".join(render_b_sweep(branch, a) for a in branch.a_range)
    return f"""-- Algebra/{branch.stem}_classification_generated.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.

module Algebra.{branch.stem}_classification_generated

import Algebra.{branch.stem}_box_cases_generated

{c_sweeps}
{b_sweeps}
{render_classifier_final(branch)}"""


def classification_c_sweep_chunks(branch: Branch) -> list[list[tuple[int, int]]]:
    pairs = list(itertools.product(branch.a_range, branch.b_range))
    if branch.classification_chunk_size is None:
        return [pairs]
    size = branch.classification_chunk_size
    assert size > 0
    return [pairs[start : start + size] for start in range(0, len(pairs), size)]


def classification_c_sweep_chunk_stem(branch: Branch, index: int) -> str:
    return f"{branch.stem}_classification_c_sweeps_{index + 1:02d}_generated"


def classification_b_sweep_stem(branch: Branch) -> str:
    return f"{branch.stem}_classification_b_sweeps_generated"


def render_classification_c_sweep_chunk(
    branch: Branch, index: int, pairs: list[tuple[int, int]], chunk_count: int
) -> str:
    stem = classification_c_sweep_chunk_stem(branch, index)
    sweeps = "\n".join(render_c_sweep(branch, a, b) for a, b in pairs)
    return f"""-- Algebra/{stem}.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.
-- Classification c-sweep chunk {index + 1} of {chunk_count}: {len(pairs)} fixed (a,b) pairs.

module Algebra.{stem}

import Algebra.{branch.stem}_box_cases_generated

{sweeps}"""


def render_classification_b_sweeps(branch: Branch, c_chunk_count: int) -> str:
    stem = classification_b_sweep_stem(branch)
    imports = "\n".join(
        f"import Algebra.{classification_c_sweep_chunk_stem(branch, index)}"
        for index in range(c_chunk_count)
    )
    sweeps = "\n".join(render_b_sweep(branch, a) for a in branch.a_range)
    return f"""-- Algebra/{stem}.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.
-- The b sweeps depend on the complete preceding layer of c sweeps.

module Algebra.{stem}

{imports}

{sweeps}"""


def render_classification_final(branch: Branch) -> str:
    return f"""-- Algebra/{branch.stem}_classification_generated.math
-- Generated by scripts/generate_rank_four_weighted_diagonal_branches.py --branch {branch.key}.  Do not edit.
-- The final a sweep depends on the complete preceding layer of b sweeps.

module Algebra.{branch.stem}_classification_generated

import Algebra.{classification_b_sweep_stem(branch)}

{render_classifier_final(branch)}"""


RENDERERS = {
    "normal_forms": render_normal_forms,
    "certificates": render_certificates,
    "cases": render_cases,
    "classifier": render_classifier,
}


def render_section_outputs(branch: Branch, section: str) -> dict[Path, str]:
    output = branch.outputs[section]
    if section == "certificates" and branch.certificate_chunk_size is not None:
        chunks = certificate_chunks(branch)
        rendered = {output: render_certificate_aggregate(branch, len(chunks))}
        for index, borders in enumerate(chunks):
            path = output.parent / f"{certificate_chunk_stem(branch, index)}.math"
            rendered[path] = render_certificate_chunk(branch, index, borders, len(chunks))
        return rendered
    if section == "cases" and branch.box_case_chunk_size is not None:
        chunks = box_case_chunks(branch)
        rendered = {output: render_box_case_aggregate(branch, len(chunks))}
        for index, cases in enumerate(chunks):
            path = output.parent / f"{box_case_chunk_stem(branch, index)}.math"
            rendered[path] = render_box_case_chunk(branch, index, cases, len(chunks))
        return rendered
    if section == "classifier" and branch.classification_chunk_size is not None:
        chunks = classification_c_sweep_chunks(branch)
        rendered = {output: render_classification_final(branch)}
        b_path = output.parent / f"{classification_b_sweep_stem(branch)}.math"
        rendered[b_path] = render_classification_b_sweeps(branch, len(chunks))
        for index, pairs in enumerate(chunks):
            path = output.parent / f"{classification_c_sweep_chunk_stem(branch, index)}.math"
            rendered[path] = render_classification_c_sweep_chunk(branch, index, pairs, len(chunks))
        return rendered
    return {output: RENDERERS[section](branch)}


def stale_section_chunks(branch: Branch, section: str, expected: set[Path]) -> set[Path]:
    base = branch.outputs["certificates"].parent
    if section == "certificates" and branch.certificate_chunk_size is not None:
        pattern = f"{branch.stem}_certificates_*_generated.math"
    elif section == "cases" and branch.box_case_chunk_size is not None:
        pattern = f"{branch.stem}_box_cases_*_generated.math"
    elif section == "classifier" and branch.classification_chunk_size is not None:
        c_pattern = f"{branch.stem}_classification_c_sweeps_*_generated.math"
        b_path = base / f"{classification_b_sweep_stem(branch)}.math"
        found = set(base.glob(c_pattern))
        if b_path.exists():
            found.add(b_path)
        return found - expected
    else:
        return set()
    return set(base.glob(pattern)) - expected


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", choices=BRANCHES)
    parser.add_argument("--section", choices=RENDERERS)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    branches = [BRANCHES[args.branch]] if args.branch else list(BRANCHES.values())
    sections = [args.section] if args.section else list(RENDERERS)
    if args.stdout and (len(branches) != 1 or len(sections) != 1):
        parser.error("--stdout requires one --branch and one --section")
    if args.stdout:
        rendered = render_section_outputs(branches[0], sections[0])
        if len(rendered) != 1:
            parser.error("--stdout cannot represent a section split across multiple files")
        sys.stdout.write(next(iter(rendered.values())))
        return 0
    for branch in branches:
        for section in sections:
            outputs = render_section_outputs(branch, section)
            stale = stale_section_chunks(branch, section, set(outputs))
            if args.check:
                mismatches = [
                    output
                    for output, rendered in outputs.items()
                    if not output.exists() or output.read_text() != rendered
                ]
                problems = [*mismatches, *sorted(stale)]
                if problems:
                    for output in problems:
                        print(f"stale generated file: {output}", file=sys.stderr)
                    return 1
            else:
                for output, rendered in outputs.items():
                    output.write_text(rendered)
                    print(f"wrote {output}")
                for output in sorted(stale):
                    output.unlink()
                    print(f"removed {output}")
        if not args.check:
            print(f"{branch.key}: {branch.expected_borders} borders, {branch.expected_normal_forms} normal forms")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Generate residue-local finite certificates for determinant-seven covers.

The residue cover chooses a concrete shift t for each admissible residue
class a modulo 588.  If the large-residual argument is unavailable, then
n <= m*t^2.  Writing n = 588*q+a leaves only a short quotient table.

The search in this script is untrusted: every emitted vector is passed to
Matrix.represents_by_witness, and its scalar value is checked by the kernel.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT_DIR = ROOT / "library" / "Algebra"
MODULUS = 588
QUOTIENT_CHUNK_SIZE = 20
RESIDUES_PER_MODULE = 8
SELECTED_CHUNK_SIZE = 12


@dataclass(frozen=True)
class Form:
    slug: str
    residue_slug: str
    residue: int
    corner: int
    multiplier: int
    choices: tuple[int, ...]
    selected: str
    expected_sources: int
    expected_finite_targets: int


FORMS = (
    Form("q0c7", "m7", 0, 7, 7, (1, 2, 3, 4, 6), "DetSevenSelectedM7", 117, 2),
    Form("q1c6", "m266", 1, 6, 266, (1, 2, 3, 4, 5, 6), "DetSevenSelectedM266", 117, 147),
    Form("q2c8", "m280", 2, 8, 280, (1, 2, 3, 4, 6, 9), "DetSevenSelectedM280", 117, 234),
    Form("q2c9", "m329", 2, 9, 329, (1, 2, 3, 4, 6, 9), "DetSevenSelectedM329", 117, 247),
    Form("q3c10", "m238", 3, 10, 238, (1, 2, 3, 4, 5, 6), "DetSevenSelectedM238", 117, 131),
    Form("q3c11", "m287", 3, 11, 287, (1, 2, 3, 4, 6, 9), "DetSevenSelectedM287", 117, 237),
)

PILOT_SLUGS = ("q0c7", "q2c9")


def safe(value: int) -> bool:
    return value % 12 not in (7, 10) and value % 49 not in (0, 21, 35, 42)


def source(value: int) -> bool:
    return value % 4 != 0 and value % 49 != 0 and not safe(value)


def selected_shift(form: Form, residue: int) -> int:
    for shift in form.choices:
        if safe((residue - form.multiplier * shift * shift) % MODULUS):
            return shift
    raise AssertionError((form.slug, residue))


def selected_pairs(form: Form) -> list[tuple[int, int]]:
    result = [
        (residue, selected_shift(form, residue))
        for residue in range(MODULUS)
        if source(residue)
    ]
    assert len(result) == form.expected_sources
    return result


def floor_sqrt(value: int) -> int:
    assert value >= 0
    low, high = 0, value + 1
    while low + 1 < high:
        middle = (low + high) // 2
        if middle * middle <= value:
            low = middle
        else:
            high = middle
    return low


def witnesses(form: Form, maximum: int) -> list[tuple[int, int, int, int] | None]:
    determinant_factor = 7 * form.corner - 4 * form.residue * form.residue
    assert determinant_factor > 0
    w_limit = floor_sqrt((7 * maximum) // determinant_factor) + 1
    shifted_z_limit = floor_sqrt(14 * maximum) + 2
    shifted_y_limit = floor_sqrt(2 * maximum) + 2

    first_triple: list[tuple[int, int, int] | None] = [None] * (maximum + 1)
    for w in range(-w_limit, w_limit + 1):
        z_low = (form.residue * w - shifted_z_limit + 6) // 7
        z_high = (form.residue * w + shifted_z_limit) // 7
        for z in range(z_low, z_high + 1):
            y_low = (-shifted_y_limit - z - form.residue * w + 1) // 2
            y_high = (shifted_y_limit - z - form.residue * w) // 2
            for y in range(y_low, y_high + 1):
                partial = (
                    2 * y * y
                    + 2 * y * z
                    + 4 * z * z
                    + 2 * form.residue * y * w
                    + form.corner * w * w
                )
                if 0 <= partial <= maximum and first_triple[partial] is None:
                    first_triple[partial] = (y, z, w)

    result: list[tuple[int, int, int, int] | None] = [None] * (maximum + 1)
    for partial, triple in enumerate(first_triple):
        if triple is None:
            continue
        x = 0
        while partial + x * x <= maximum:
            target = partial + x * x
            if result[target] is None:
                result[target] = (x, *triple)
            x += 1
    for target in range(1, maximum + 1):
        assert result[target] is not None, (form.slug, target)
    return result


def integer(value: int) -> str:
    return str(value)


def scalar_integer(value: int) -> str:
    return str(value) if value >= 0 else f"({value} : ℤ)"


def vector(vector_value: tuple[int, int, int, int]) -> str:
    return "⟨" + ", ".join(integer(value) for value in vector_value) + "⟩"


def scalar_expression(form: Form, vector_value: tuple[int, int, int, int]) -> str:
    x, y, z, w = (scalar_integer(value) for value in vector_value)
    return (
        f"({x} : ℤ) * {x} + 2 * ({y} * {y}) + 2 * {y} * {z} + 4 * ({z} * {z}) "
        f"+ 2 * {form.residue} * {y} * {w} + {form.corner} * ({w} * {w})"
    )


def theorem_stem(form: Form, residue: int, shift: int) -> str:
    return f"detSevenFinite{form.slug.upper()}A{residue}T{shift}"


def representation_goal(form: Form, n: str = "n") -> str:
    return (
        "Matrix.Represents("
        f"Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, {form.residue}, {form.corner}), "
        f"({n} : ℤ))"
    )


def render_part(
    form: Form,
    residue: int,
    shift: int,
    lower: int,
    upper: int,
    witness_table: list[tuple[int, int, int, int] | None],
) -> str:
    stem = theorem_stem(form, residue, shift)
    facts = []
    for quotient in range(lower, upper):
        target = MODULUS * quotient + residue
        witness = witness_table[target]
        assert witness is not None
        facts.append(
            f"""  {scalar_expression(form, witness)} = ({target} : ℤ) as scalarComputation;
  Matrix.represents_by_witness(A, target := {target}, vector := {vector(witness)},
    computes := Matrix.detSevenRankFour_coordinateTuple_computes(scalarComputation := scalarComputation));"""
        )
    return f"""theorem Matrix.{stem}_part{lower // QUOTIENT_CHUNK_SIZE}
        : ∀ (q : ℕ). q ≥ {lower} → q < {upper} →
          Matrix.Represents(
            Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, {form.residue}, {form.corner}),
            (588 : ℤ) * (q : ℤ) + ({residue} : ℤ)) := {{
  let A : Matrix(Integer.commutative_ring_bundle, 4, 4) :=
    Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, {form.residue}, {form.corner});
{chr(10).join(facts)}
  done by finite_check q from {lower} until {upper}
}}"""


def render_quotient_dispatch(
    form: Form,
    residue: int,
    shift: int,
    count: int,
    indent: str,
) -> str:
    stem = theorem_stem(form, residue, shift)
    boundaries = list(range(QUOTIENT_CHUNK_SIZE, count, QUOTIENT_CHUNK_SIZE))

    def dispatch(index: int, lower: int, lower_proof: str, depth: str) -> str:
        if index == len(boundaries):
            return (
                f"{depth}done by Matrix.{stem}_part{lower // QUOTIENT_CHUNK_SIZE}("
                f"q, {lower_proof}, qBelow)"
            )
        boundary = boundaries[index]
        return f"""{depth}q < {boundary} ∨ {boundary} ≤ q by Natural.lt_or_le;
{depth}done by cases {{
{depth}  case q < {boundary} as below{boundary}:
{depth}    done by Matrix.{stem}_part{lower // QUOTIENT_CHUNK_SIZE}(q, {lower_proof}, below{boundary})
{depth}  case {boundary} ≤ q as atLeast{boundary}: {{
{dispatch(index + 1, boundary, f"atLeast{boundary}", depth + "    ")}
{depth}  }}
{depth}}}"""

    return dispatch(0, 0, "done", indent)


def render_residue_declarations(
    form: Form,
    residue: int,
    shift: int,
    witness_table: list[tuple[int, int, int, int] | None],
) -> str:
    bound = form.multiplier * shift * shift
    if residue > bound:
        return ""
    count = (bound - residue) // MODULUS + 1
    declarations = []
    for lower in range(0, count, QUOTIENT_CHUNK_SIZE):
        declarations.append(
            render_part(
                form,
                residue,
                shift,
                lower,
                min(lower + QUOTIENT_CHUNK_SIZE, count),
                witness_table,
            )
        )
    stem = theorem_stem(form, residue, shift)
    dispatch = render_quotient_dispatch(form, residue, shift, count, "  ")
    declarations.append(
        f"""theorem Matrix.{stem}
        (n : ℕ) (positive : n ≥ 1)
        (bounded : n ≤ {bound})
        (remainderReads : Natural.modulo(n, 588) = {residue})
        : Matrix.Represents(
            Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, {form.residue}, {form.corner}),
            (n : ℤ)) := {{
  let q : ℕ := Natural.floor_divide(n, 588);
  588 * q + Natural.modulo(n, 588) = n
      by Natural.floor_divide_modulo_decompose;
  588 * q + {residue} = n by substituting remainderReads as exactDecomposition;
  q < {count} by Natural.quotient_below_of_bounded_decomposition(
    588, q, {residue}, n, {bound}, {count}, done, exactDecomposition, bounded)
  as qBelow;
  Matrix.Represents(
      Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, {form.residue}, {form.corner}),
      (588 : ℤ) * (q : ℤ) + ({residue} : ℤ)) by {{
{dispatch}
  }};
  (588 : ℤ) * (q : ℤ) + ({residue} : ℤ)
     = ((588 * q : ℕ) : ℤ) + ({residue} : ℤ)
         by substituting Equality.symmetry(Natural.to_integer.multiply_preserves(588, q))
     = ((588 * q + {residue} : ℕ) : ℤ)
         by Equality.symmetry(Natural.to_integer.add_preserves(588 * q, {residue}))
     = (n : ℤ) by substituting exactDecomposition
  as integerDecomposition;
  done by substituting integerDecomposition
}}"""
    )
    return "\n\n".join(declarations)


def render_module(form: Form, index: int, declarations: list[str]) -> str:
    return f"""-- Generated by scripts/generate_det_seven_finite_covers.py. Do not edit.
-- Explicit quotient-table witnesses for {form.slug}.

module Algebra.det_seven_finite_{form.slug}_tables_chunk{index}_generated

import Algebra.det_seven_rank_four_infrastructure

{chr(10).join(chr(10) + declaration for declaration in declarations)}
"""


def pair_branch(form: Form, residue: int, shift: int, indent: str) -> str:
    bound = form.multiplier * shift * shift
    common = f"""{indent}a = {residue} by And.left(a = {residue}, t = {shift}, selectedPair) as aReads;
{indent}t = {shift} by And.right(a = {residue}, t = {shift}, selectedPair) as tReads;
{indent}n ≤ {bound} by substituting tReads;
{indent}Natural.modulo(n, 588) = {residue} by substituting aReads as exactRemainder;"""
    if residue <= bound:
        return (
            common
            + f"\n{indent}done by Matrix.{theorem_stem(form, residue, shift)}("
            "n, positive, done, exactRemainder)"
        )
    return (
        common
        + f"""\n{indent}{residue} ≤ n by Natural.remainder_le_of_modulo_eq(
{indent}  n, 588, {residue}, exactRemainder);
{indent}{residue} < {residue} by {{
{indent}  {residue} ≤ n ≤ {bound} < {residue};
{indent}  done
{indent}}};
{indent}False by Natural.lt_irreflexive;
{indent}done"""
    )


def render_pair_cases(form: Form, pairs: list[tuple[int, int]], indent: str) -> str:
    rendered = []
    for residue, shift in pairs:
        body = pair_branch(form, residue, shift, indent + "    ")
        rendered.append(
            f"""{indent}case a = {residue} ∧ t = {shift} as selectedPair: {{
{body}
{indent}}}"""
        )
    return "\n".join(rendered)


def render_selected_cases(form: Form, pairs: list[tuple[int, int]], indent: str) -> str:
    chunks = [
        pairs[index : index + SELECTED_CHUNK_SIZE]
        for index in range(0, len(pairs), SELECTED_CHUNK_SIZE)
    ]
    rendered = []
    for index, chunk in enumerate(chunks):
        pair_disjunction = " ∨ ".join(f"(a = {a} ∧ t = {t})" for a, t in chunk)
        pair_cases = render_pair_cases(form, chunk, indent + "    ")
        rendered.append(
            f"""{indent}case Natural.{form.selected}Chunk{index}(a, t) as selectedChunk: {{
{indent}  {pair_disjunction}
{indent}      by unfold Natural.{form.selected}Chunk{index} in selectedChunk;
{indent}  {representation_goal(form)} by cases {{
{pair_cases}
{indent}  }}
{indent}}}"""
        )
    return "\n".join(rendered)


def render_aggregate(form: Form, module_count: int, pairs: list[tuple[int, int]]) -> str:
    imports = "\n".join(
        f"import Algebra.det_seven_finite_{form.slug}_tables_chunk{index}_generated"
        for index in range(module_count)
    )
    chunk_disjunction = " ∨ ".join(
        f"Natural.{form.selected}Chunk{index}(a, t)"
        for index in range((len(pairs) + SELECTED_CHUNK_SIZE - 1) // SELECTED_CHUNK_SIZE)
    )
    cases = render_selected_cases(form, pairs, "      ")
    return f"""-- Generated by scripts/generate_det_seven_finite_covers.py. Do not edit.
-- Residue-local finite cover for {form.slug}; {form.expected_finite_targets} explicit targets.

module Algebra.det_seven_finite_{form.slug}_generated

import Algebra.det_seven_residual_{form.residue_slug}_generated
{imports}

theorem Matrix.detSevenFiniteCover_{form.slug}
        : Matrix.DetSevenFiniteCover(
            Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, {form.residue}, {form.corner}),
            {form.multiplier}, Natural.{form.selected}) := {{
  unfold Matrix.DetSevenFiniteCover in {{
    take a : ℕ;
    take t : ℕ;
    take n : ℕ;
    suppose Natural.{form.selected}(a, t) as selected;
    suppose n ≥ 1 as positive;
    suppose n ≤ {form.multiplier} * t * t as bounded;
    suppose Natural.modulo(n, 588) = a as remainderReads;
    {chunk_disjunction}
        by unfold Natural.{form.selected} in selected;
    {representation_goal(form)} by cases {{
{cases}
    }}
  }}
}}
"""


def generated_files(form: Form) -> dict[Path, str]:
    pairs = selected_pairs(form)
    maximum = form.multiplier * max(form.choices) ** 2
    witness_table = witnesses(form, maximum)
    residue_units = []
    target_count = 0
    for residue, shift in pairs:
        bound = form.multiplier * shift * shift
        if residue <= bound:
            target_count += (bound - residue) // MODULUS + 1
        unit = render_residue_declarations(form, residue, shift, witness_table)
        if unit:
            residue_units.append(unit)
    assert target_count == form.expected_finite_targets, (form.slug, target_count)
    chunks = [
        residue_units[index : index + RESIDUES_PER_MODULE]
        for index in range(0, len(residue_units), RESIDUES_PER_MODULE)
    ]
    result = {
        OUTPUT_DIR / f"det_seven_finite_{form.slug}_tables_chunk{index}_generated.math":
            render_module(form, index, chunk)
        for index, chunk in enumerate(chunks)
    }
    result[OUTPUT_DIR / f"det_seven_finite_{form.slug}_generated.math"] = (
        render_aggregate(form, len(chunks), pairs)
    )
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--forms",
        default="pilot",
        help="pilot, all, or a comma-separated list of form slugs",
    )
    args = parser.parse_args()
    if args.forms == "pilot":
        slugs = set(PILOT_SLUGS)
    elif args.forms == "all":
        slugs = {form.slug for form in FORMS}
    else:
        slugs = set(args.forms.split(","))
    forms = [form for form in FORMS if form.slug in slugs]
    if len(forms) != len(slugs):
        raise SystemExit(f"unknown form slug in {args.forms}")

    stale = []
    for form in forms:
        for path, expected in generated_files(form).items():
            if args.check:
                if not path.exists() or path.read_text() != expected:
                    stale.append(path)
            elif not path.exists() or path.read_text() != expected:
                path.write_text(expected)
    if stale:
        for path in stale:
            print(f"stale generated file: {path}")
        return 1
    if args.check:
        print(f"det-seven-finite-generated-check ({args.forms}): PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

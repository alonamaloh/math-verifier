#!/usr/bin/env python3
"""Generate the seven kernel-checked modulo-588 residual covers."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT_DIR = ROOT / "library" / "Algebra"
MODULUS = 588
CHUNKS = tuple((lower, lower + 49) for lower in range(0, MODULUS, 49))
SELECTED_CHUNK_SIZE = 12


@dataclass(frozen=True)
class Row:
    slug: str
    theorem: str
    multiplier: int
    choices: tuple[int, ...]
    choice_predicate: str
    odd_only: bool = False


ROWS = (
    Row("m7", "detSevenResidueCover_m7", 7, (1, 2, 3, 4, 6), "DetSevenChoices12346"),
    Row("m266", "detSevenResidueCover_m266", 266, (1, 2, 3, 4, 5, 6), "DetSevenChoices123456"),
    Row("m280", "detSevenResidueCover_m280", 280, (1, 2, 3, 4, 6, 9), "DetSevenChoices123469"),
    Row("m329", "detSevenResidueCover_m329", 329, (1, 2, 3, 4, 6, 9), "DetSevenChoices123469"),
    Row("m238", "detSevenResidueCover_m238", 238, (1, 2, 3, 4, 5, 6), "DetSevenChoices123456"),
    Row("m287", "detSevenResidueCover_m287", 287, (1, 2, 3, 4, 6, 9), "DetSevenChoices123469"),
    Row(
        "m315_odd",
        "detSevenOddResidueCover_m315",
        315,
        (1, 2, 3, 4, 5, 6),
        "DetSevenChoices123456",
        odd_only=True,
    ),
)


def safe(value: int) -> bool:
    return value % 12 not in (7, 10) and value % 49 not in (0, 21, 35, 42)


def source(row: Row, value: int) -> bool:
    parity_condition = value % 2 == 1 if row.odd_only else value % 4 != 0
    return parity_condition and value % 49 != 0 and not safe(value)


def integer_literal(value: int) -> str:
    return f"({value} : ℤ)" if value >= 0 else f"(-{-value} : ℤ)"


def solve(row: Row, value: int) -> tuple[int, int, int]:
    for choice in row.choices:
        difference = value - row.multiplier * choice * choice
        residue = difference % MODULUS
        if safe(residue):
            quotient = (difference - residue) // MODULUS
            return choice, residue, quotient
    raise AssertionError(f"uncovered residue {value} for multiplier {row.multiplier}")


def selected_name(row: Row) -> str:
    if row.odd_only:
        return "DetSevenSelectedM315Odd"
    return f"DetSevenSelectedM{row.multiplier}"


def selected_definitions(row: Row, source_values: list[int]) -> str:
    name = selected_name(row)
    chunks = [
        source_values[index : index + SELECTED_CHUNK_SIZE]
        for index in range(0, len(source_values), SELECTED_CHUNK_SIZE)
    ]
    definitions = []
    for index, values in enumerate(chunks):
        pairs = "\n  ∨ ".join(
            f"(a = {value} ∧ t = {solve(row, value)[0]})" for value in values
        )
        definitions.append(
            f"""definition Natural.{name}Chunk{index} (a t : ℕ) : Proposition :=
  {pairs}"""
        )
    top = "\n  ∨ ".join(
        f"Natural.{name}Chunk{index}(a, t)" for index in range(len(chunks))
    )
    definitions.append(
        f"""definition Natural.{name} (a t : ℕ) : Proposition :=
  {top}"""
    )
    return "\n\n".join(definitions)


def selected_chunk_index(row: Row, value: int) -> int:
    source_values = [candidate for candidate in range(MODULUS) if source(row, candidate)]
    return source_values.index(value) // SELECTED_CHUNK_SIZE


def render_fact(row: Row, value: int) -> str:
    choice, residue, quotient = solve(row, value)
    return f"""  Natural.DetSevenResidueSolution({row.multiplier}, {value}, {choice}) by
    Natural.detSevenResidueSolution_of_certificate(
      {row.multiplier}, {value}, {choice}, {residue}, {integer_literal(quotient)},
      done, done, done);"""


def render_case(row: Row, value: int, choice_disjunction: str) -> str:
    parity_condition = (
        f"Natural.modulo({value}, 2) = 1"
        if row.odd_only
        else f"Natural.modulo({value}, 4) ≠ 0"
    )
    proposition = f"""{parity_condition} →
    Natural.modulo({value}, 49) ≠ 0 →
    ¬(Natural.IsDetSevenSafe({value})) →
    ∃ (t : ℕ). ({choice_disjunction})
      ∧ Natural.{selected_name(row)}({value}, t)
      ∧ Natural.DetSevenResidueSolution({row.multiplier}, {value}, t)"""
    introductions = f"""    suppose {parity_condition};
    suppose Natural.modulo({value}, 49) ≠ 0;
    suppose ¬(Natural.IsDetSevenSafe({value}));"""
    if source(row, value):
        choice, _, _ = solve(row, value)
        choice_ground = choice_disjunction.replace("t =", f"{choice} =")
        chunk = selected_chunk_index(row, value)
        return f"""{render_fact(row, value)}
  {proposition} by {{
{introductions}
    witness {choice} with {{
      {choice_ground};
      {value} = {value} ∧ {choice} = {choice} as selectedPair;
      Natural.{selected_name(row)}Chunk{chunk}({value}, {choice})
          by {{
            unfold Natural.{selected_name(row)}Chunk{chunk} in {{
              done by disjunct(selectedPair)
            }}
          }}
          as selectedChunk;
      Natural.{selected_name(row)}({value}, {choice})
          by {{
            unfold Natural.{selected_name(row)} in {{
              done by disjunct(selectedChunk)
            }}
          }};
      Natural.DetSevenResidueSolution({row.multiplier}, {value}, {choice});
      done
    }}
  }};"""
    if row.odd_only and value % 2 != 1:
        contradiction = f"""    Natural.modulo({value}, 2) ≠ 1 by done;
    done"""
    elif not row.odd_only and value % 4 == 0:
        contradiction = f"""    Natural.modulo({value}, 4) = 0 by done;
    done"""
    elif value % 49 == 0:
        contradiction = f"""    Natural.modulo({value}, 49) = 0 by done;
    done"""
    else:
        assert safe(value)
        contradiction = f"""    Natural.IsDetSevenSafe({value})
        by unfolding Natural.IsDetSevenSafe;
    done"""
    return f"""  {proposition} by {{
{introductions}
{contradiction}
  }};"""


def render_dispatch(row: Row, index: int, lower_proof: str, indent: str) -> str:
    lower, upper = CHUNKS[index]
    if index == len(CHUNKS) - 1:
        return (
            f"{indent}done by Natural.{row.theorem}_selected_table_part{index}(\n"
            f"{indent}  a, {lower_proof}, aBelow, parityCondition, "
            "notMultipleFortyNine, unsafe)"
        )
    in_range = f"below{upper}"
    after = f"atLeast{upper}"
    rest = render_dispatch(row, index + 1, after, indent + "    ")
    return f"""{indent}a < {upper} ∨ {upper} ≤ a by Natural.lt_or_le;
{indent}done by cases {{
{indent}  case a < {upper} as {in_range}:
{indent}    done by Natural.{row.theorem}_selected_table_part{index}(
{indent}      a, {lower_proof}, {in_range}, parityCondition, notMultipleFortyNine, unsafe)
{indent}  case {upper} ≤ a as {after}: {{
{rest}
{indent}  }}
{indent}}}"""


def render(row: Row) -> str:
    source_values = [value for value in range(MODULUS) if source(row, value)]
    solved_counts = []
    for choice in row.choices:
        solved_counts.append(sum(1 for value in source_values if solve(row, value)[0] == choice))
    expected = (48, 5, 6, 1, 2, 1) if row.odd_only else {
        7: (100, 10, 5, 1, 1),
        266: (94, 9, 10, 1, 2, 1),
        280: (93, 9, 7, 4, 2, 2),
        329: (94, 9, 9, 2, 1, 2),
        238: (94, 9, 10, 1, 2, 1),
        287: (93, 9, 8, 3, 2, 2),
    }[row.multiplier]
    assert tuple(solved_counts) == expected
    cover = "DetSevenOddResidueCover" if row.odd_only else "DetSevenGenericResidueCover"
    parity_condition = (
        "Natural.modulo(a, 2) = 1" if row.odd_only else "Natural.modulo(a, 4) ≠ 0"
    )
    choice_disjunction = " ∨ ".join(f"t = {choice}" for choice in row.choices)
    unsafe_condition = """¬(
            Natural.modulo(a, 12) ≠ 7
            ∧ Natural.modulo(a, 12) ≠ 10
            ∧ Natural.modulo(a, 49) ≠ 0
            ∧ Natural.modulo(a, 49) ≠ 21
            ∧ Natural.modulo(a, 49) ≠ 35
            ∧ Natural.modulo(a, 49) ≠ 42)"""
    chunk_blocks = []
    for index, (lower, upper) in enumerate(CHUNKS):
        facts = "\n".join(
            render_case(row, value, choice_disjunction) for value in range(lower, upper)
        )
        chunk_blocks.append(
            f"""theorem Natural.{row.theorem}_selected_table_part{index}
        : ∀ (a : ℕ). a ≥ {lower} → a < {upper} →
          {parity_condition} →
          Natural.modulo(a, 49) ≠ 0 →
          {unsafe_condition} →
          ∃ (t : ℕ). ({choice_disjunction})
            ∧ Natural.{selected_name(row)}(a, t)
            ∧ Natural.DetSevenResidueSolution({row.multiplier}, a, t) := {{
{facts}
  done by finite_check a from {lower} until {upper}
}}"""
        )
    chunks = "\n\n".join(chunk_blocks)
    dispatch = render_dispatch(row, 0, "aNonnegative", "  ")
    return f"""-- Generated by scripts/generate_det_seven_residual_covers.py. Do not edit.
-- multiplier={row.multiplier}; source residues={len(source_values)};
-- first-solved counts={','.join(str(count) for count in solved_counts)}.

module Algebra.det_seven_residual_{row.slug}_generated

import Algebra.det_seven_residual_arithmetic

{selected_definitions(row, source_values)}

{chunks}

theorem Natural.{row.theorem}_selected_table
        : ∀ (a : ℕ). a ≥ 0 → a < 588 →
          {parity_condition} →
          Natural.modulo(a, 49) ≠ 0 →
          {unsafe_condition} →
          ∃ (t : ℕ). ({choice_disjunction})
            ∧ Natural.{selected_name(row)}(a, t)
            ∧ Natural.DetSevenResidueSolution({row.multiplier}, a, t) := {{
  take a : ℕ;
  suppose a ≥ 0 as aNonnegative;
  suppose a < 588 as aBelow;
  suppose {parity_condition} as parityCondition;
  suppose Natural.modulo(a, 49) ≠ 0 as notMultipleFortyNine;
  suppose {unsafe_condition} as unsafe;
{dispatch}
}}

theorem Natural.{row.theorem}_table
        : ∀ (a : ℕ). a ≥ 0 → a < 588 →
          {parity_condition} →
          Natural.modulo(a, 49) ≠ 0 →
          {unsafe_condition} →
          ∃ (t : ℕ). ({choice_disjunction})
            ∧ Natural.DetSevenResidueSolution({row.multiplier}, a, t) := {{
  take a : ℕ;
  suppose a ≥ 0 as aNonnegative;
  suppose a < 588 as aBelow;
  suppose {parity_condition} as parityCondition;
  suppose Natural.modulo(a, 49) ≠ 0 as notMultipleFortyNine;
  suppose {unsafe_condition} as unsafe;
  choose t : ℕ such that
      ({choice_disjunction})
      ∧ Natural.{selected_name(row)}(a, t)
      ∧ Natural.DetSevenResidueSolution({row.multiplier}, a, t)
      from Natural.{row.theorem}_selected_table(
        a, aNonnegative, aBelow, parityCondition, notMultipleFortyNine, unsafe);
  witness t with {{
    ({choice_disjunction});
    Natural.DetSevenResidueSolution({row.multiplier}, a, t);
    done
  }}
}}

theorem Natural.{row.theorem}
        : Natural.{cover}(
            {row.multiplier}, Natural.{row.choice_predicate}) := {{
  unfold Natural.{cover}, Natural.{row.choice_predicate}, Natural.IsDetSevenSafe in {{
    done by Natural.{row.theorem}_table
  }}
}}

theorem Natural.{row.theorem}_selected
        : Natural.{"DetSevenOddSelectedResidueCover" if row.odd_only else "DetSevenGenericSelectedResidueCover"}(
            {row.multiplier}, Natural.{row.choice_predicate}, Natural.{selected_name(row)}) := {{
  unfold Natural.{"DetSevenOddSelectedResidueCover" if row.odd_only else "DetSevenGenericSelectedResidueCover"},
      Natural.{row.choice_predicate}, Natural.IsDetSevenSafe in {{
    done by Natural.{row.theorem}_selected_table
  }}
}}
"""


def output_path(row: Row) -> Path:
    return OUTPUT_DIR / f"det_seven_residual_{row.slug}_generated.math"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    stale = []
    for row in ROWS:
        expected = render(row)
        path = output_path(row)
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
        print("det-seven-residual-generated-check: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Generate the four finite rank-four truant-15 exclusion tables.

The search is deliberately tiny and untrusted: it substitutes the bounded
last two coordinates into a completed-square identity.  Every emitted leaf,
collector, nonrepresentation theorem, and exact-truant theorem is checked by
the kernel.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "library/Algebra/rank_four_exceptional_truants_generated.math"


@dataclass(frozen=True)
class Form:
    stem: str
    second: int
    third: int
    corner: int
    completion: int
    second_coefficient: int
    z_low: int
    z_high: int
    coordinate_bound: str
    positive_table: str


FORMS = (
    Form("weightedD5S0R0C5", 0, 0, 5, 50, 10, -1, 2,
         "Integer.weightedD5R0C10_coordinate_bound", "Matrix.weightedD5S0R0C5_represents_below_fifteen"),
    Form("weightedD5S1R1C5", 1, 1, 5, 43, 9, -2, 3,
         "Integer.weightedD5R1_coordinate_bound", "Matrix.weightedD5S1R1C5_represents_below_fifteen"),
    Form("weightedD5S1R1C9", 1, 1, 9, 83, 17, -2, 3,
         "Integer.weightedD5R1_coordinate_bound", "Matrix.weightedD5S1R1C9_represents_below_fifteen"),
    Form("weightedD5S1R2C8", 1, 2, 8, 67, 15, -3, 4,
         "Integer.weightedD5R2C15_coordinate_bound", "Matrix.weightedD5S1R2C8_represents_below_fifteen"),
)


def integer(value: int) -> str:
    return str(value) if value >= 0 else f"(-({-value} : ℤ))"


def expression(form: Form, z: str, w: str) -> str:
    return (f"2 * (x * x) + u * u + 10 * ({z} * {z}) + 4 * {form.third} * {z} * {w}\n"
            f"          + {form.second_coefficient} * ({w} * {w}) = 30")


def leaf(form: Form, z: int, w: int) -> str:
    residual = 30 - (10 * z * z + 4 * form.third * z * w + form.second_coefficient * w * w)
    goal = expression(form, integer(z), integer(w))
    if residual >= 0:
        assert residual in {7, 10, 13, 14, 15, 20, 21, 30}
        return (f"  ¬({goal})\n"
                f"      by Integer.weightedD5_completed_excludes_exceptional_residual(target := {residual});")
    return (f"  ¬({goal})\n"
            f"      by Integer.weightedD5_completed_excludes_negative_residual(residual := ({residual} : ℤ));")


def row(form: Form, w: int, label: str) -> str:
    leaves = "\n".join(leaf(form, z, w) for z in range(form.z_low, form.z_high))
    quantified = expression(form, "q", integer(w))
    return (f"{leaves}\n"
            f"  ∀ (q : ℤ). {form.z_low} ≤ q → q < {form.z_high} → ¬({quantified})\n"
            f"      by finite_check q from {form.z_low} until {form.z_high} as {label};")


def exclusion(form: Form) -> str:
    rows = "\n".join((row(form, -1, "atMinusOne"), row(form, 0, "atZero"), row(form, 1, "atOne")))
    actual_minus = expression(form, "z", "(-1)")
    actual_zero = expression(form, "z", "0")
    actual_one = expression(form, "z", "1")
    actual = expression(form, "z", "p")
    return f"""theorem Integer.{form.stem}_finite_exclusion
        (x u w z : ℤ) (wLower : -1 ≤ w) (wUpper : w < 2)
        (zLower : {form.z_low} ≤ z) (zUpper : z < {form.z_high})
        : ¬({expression(form, 'z', 'w')}) := {{
{rows}
  ¬({actual_minus}) by atMinusOne(z, zLower, zUpper);
  ¬({actual_zero}) by atZero(z, zLower, zUpper);
  ¬({actual_one}) by atOne(z, zLower, zUpper);
  ∀ (p : ℤ). -1 ≤ p → p < 2 → ¬({actual})
      by finite_check p from -1 until 2 as allRows;
  done by allRows(w, wLower, wUpper)
}}
"""


def concrete_theorems(form: Form) -> str:
    matrix = ("Matrix.squarePlusDoublePlusScaledRankFourRepresentative"
              f"(5, {form.second}, {form.third}, {form.corner})")
    if form.coordinate_bound == "Integer.weightedD5R1_coordinate_bound":
        bound_proof = (f"done by {form.coordinate_bound}(secondCoefficient := {form.second_coefficient}, "
                       "coefficientAtLeastOne := done, completed := completed)")
    else:
        bound_proof = f"done by {form.coordinate_bound}(completed := completed)"
    return f"""theorem Matrix.{form.stem}_not_represents_fifteen
        : ¬(Matrix.Represents({matrix}, (15 : ℤ))) := {{
  done by Matrix.weightedD5_not_represents_fifteen_by_completion(
    completionCoefficient := {form.completion}, secondCoefficient := {form.second_coefficient},
    zLow := {form.z_low}, zHigh := {form.z_high},
    completionCoefficientReads := (ring : (10 : ℤ) * {form.corner} - 5 * ({form.second} * {form.second})
      - 2 * ({form.third} * {form.third}) = {form.completion}),
    completionCoefficientAtLeastForty := done,
    secondCoefficientReads := (ring : (2 : ℤ) * {form.corner} - {form.second} * {form.second} = {form.second_coefficient}),
    coordinateBound := (x u z w : ℤ) (completed :
      2 * (x * x) + u * u + 10 * (z * z) + 4 * {form.third} * z * w
        + {form.second_coefficient} * (w * w) = 30) ↦ {{ {bound_proof} }},
    finiteExclusion := Integer.{form.stem}_finite_exclusion)
}}

theorem Matrix.{form.stem}_truant_fifteen
        : Matrix.IsTruant({matrix}, 15) := {{
  (15 : ℕ) ≥ 1;
  ¬(Matrix.Represents({matrix}, (15 : ℤ))) by Matrix.{form.stem}_not_represents_fifteen;
  done by {form.positive_table}
}}

theorem Matrix.{form.stem}_truant
        : Matrix.truant({matrix}) = 15 :=
  by Matrix.truant_equals
"""


def render() -> str:
    body = "\n".join(exclusion(form) + "\n" + concrete_theorems(form) for form in FORMS)
    return f"""-- Algebra/rank_four_exceptional_truants_generated.math
-- Generated by scripts/generate_rank_four_exceptional_truants.py.  Do not edit.
-- Four bounded completed-square tables; every leaf is kernel checked.

module Algebra.rank_four_exceptional_truants_generated

import Algebra.rank_four_exceptional_truants

{body}"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = render()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != expected:
            print(f"stale generated file: {OUTPUT}")
            return 1
        print("rank-four-exceptional-truants-generated-check: PASS")
        return 0
    OUTPUT.write_text(expected)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

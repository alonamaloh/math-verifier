#!/usr/bin/env python3
"""Generate the residue arithmetic the rank-three exclusion descents need.

For each modulus the library does not already carry, emit

  * `Natural.below_<m>_values`      — every value below m is one of 0 … m-1,
  * `IntegerMod.mod_<m>_cases`      — every class is one of the m residues,
  * `IntegerMod.square_mod_<m>`     — the square classes, and
  * `IntegerMod.square_zero_mod_<m>_forces_zero` (prime moduli only),

and then, over the square classes alone, the ternary residue facts the
certificates cite.  Enumerating square classes rather than raw residues is
what keeps these trees at tens of arms instead of thousands.
"""

from __future__ import annotations

import argparse
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

WORDS = {
    0: "zero", 1: "one", 2: "two", 3: "three", 4: "four", 5: "five",
    6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten", 11: "eleven",
    12: "twelve", 13: "thirteen", 14: "fourteen", 15: "fifteen",
    16: "sixteen",
}

VARIABLES = ("x", "y", "z")


def disjunction(terms: list[str], joiner: str) -> str:
    return joiner.join(terms)


def inject(index: int, count: int, proof: str) -> str:
    """Prove the index-th disjunct of a right-nested count-way disjunction."""
    if count == 1:
        return proof
    body = proof if index == count - 1 else f"Or.introduceLeft({proof})"
    for _ in range(index):
        body = f"Or.introduceRight({body})"
    return body


def case_tree(values: list[str], arms: list[str], binder: str,
              depth: int) -> str:
    """A `by cases` tree over a right-nested disjunction of `values`."""
    pad = " " * depth
    if len(values) == 1:
        return arms[0]
    head, *rest = values
    inner = case_tree(rest, arms[1:], binder, depth + 2)
    # A single remaining disjunct is a leaf: the parent must bind it, since
    # the recursive call emits only the arm body.
    rest_label = (f"{rest[0]} as {binder}" if len(rest) == 1
                  else disjunction(rest, ' ∨ '))
    return (
        "done by cases {\n"
        f"{pad}  case {head} as {binder}: {arms[0]}\n"
        f"{pad}  case {rest_label}: {inner}\n"
        f"{pad}}}"
    )


def square_classes(modulus: int) -> list[int]:
    return sorted({(value * value) % modulus for value in range(modulus)})


# ----------------------------------------------------------------------
# Value enumeration below a modulus.

def below_values(modulus: int, positive_lemma: str | None,
                 ladder_from: int | None) -> str:
    word = WORDS[modulus]
    goal = disjunction([f"r = {value}" for value in range(modulus)], "\n          ∨ ")
    if ladder_from is not None:
        lower = WORDS[ladder_from]
        lower_values = [f"r = {value}" for value in range(ladder_from)]
        arms = [f"done by {inject(index, modulus, 'rValue')}"
                for index in range(ladder_from)]
        tree = case_tree(lower_values, arms, "rValue", 6)
        return f"""theorem Natural.below_{word}_values (r : ℕ) (rBelow : r < {modulus})
        : {goal} := {{
  r < {modulus - 1} ∨ r = {modulus - 1} by Natural.below_successor_or_equal;
  done by cases {{
    case r < {modulus - 1} as lowerBound: {{
      {disjunction(lower_values, " ∨ ")}
          by Natural.below_{lower}_values;
      {tree}
    }}
    case r = {modulus - 1} as topValue: done by {inject(modulus - 1, modulus, 'topValue')}
  }}
}}
"""
    assert positive_lemma is not None
    positive_values = [f"r = {value}" for value in range(1, modulus)]
    arms = [f"done by {inject(index + 1, modulus, 'rValue')}"
            for index in range(modulus - 1)]
    tree = case_tree(positive_values, arms, "rValue", 6)
    return f"""theorem Natural.below_{word}_values (r : ℕ) (rBelow : r < {modulus})
        : {goal} := {{
  r = 0 ∨ ∃ (predecessor : ℕ). r = 1 + predecessor by Natural.zero_or_one_plus;
  done by cases {{
    case r = 0 as rValue: done by {inject(0, modulus, 'rValue')}
    case ∃ (predecessor : ℕ). r = 1 + predecessor: {{
      choose predecessor : ℕ such that r = 1 + predecessor;
      1 ≤ r by substituting (r = 1 + predecessor) as rPositive;
      {disjunction(positive_values, " ∨ ")}
          by {positive_lemma}(positive := rPositive, bound := rBelow);
      {tree}
    }}
  }}
}}
"""


# ----------------------------------------------------------------------
# Residue classes and square classes.

def mod_cases(modulus: int) -> str:
    word = WORDS[modulus]
    classes = [f"x = IntegerMod.residue({modulus}, {value})"
               for value in range(modulus)]
    values = [f"r = {value}" for value in range(modulus)]
    arms = []
    for value in range(modulus):
        chain = (
            "{\n"
            f"        x = IntegerMod.make({modulus}, (r : ℤ)) by xReads\n"
            f"           = IntegerMod.residue({modulus}, {value}) by substituting rValue;\n"
            "        done\n"
            "      }"
        )
        arms.append(f"done by {inject(value, modulus, chain)}")
    tree = case_tree(values, arms, "rValue", 2)
    class_goal = disjunction(classes, "\n          ∨ ")
    return f"""theorem IntegerMod.mod_{word}_cases (x : IntegerMod({modulus}))
        : {class_goal} := {{
  choose r such that r < {modulus} ∧ x = IntegerMod.make({modulus}, (r : ℤ))
      from IntegerMod.exists_natural_representative({modulus}, done, x);
  x = IntegerMod.make({modulus}, (r : ℤ))
      by And.right(r < {modulus}, x = IntegerMod.make({modulus}, (r : ℤ))) as xReads;
  r < {modulus} by And.left(r < {modulus}, x = IntegerMod.make({modulus}, (r : ℤ)));
  {disjunction(values, " ∨ ")}
      by Natural.below_{word}_values;
  {tree}
}}
"""


def square_mod(modulus: int) -> str:
    word = WORDS[modulus]
    squares = square_classes(modulus)
    goal = disjunction([f"x * x = IntegerMod.residue({modulus}, {square})"
                        for square in squares], "\n          ∨ ")
    values = [f"x = IntegerMod.residue({modulus}, {value})"
              for value in range(modulus)]
    arms = []
    for value in range(modulus):
        square = (value * value) % modulus
        multiple = (value * value - square) // modulus
        chain = (
            "{\n"
            "        x * x\n"
            f"           = IntegerMod.residue({modulus}, {value})"
            f" * IntegerMod.residue({modulus}, {value}) by substituting xValue\n"
            f"           = IntegerMod.residue({modulus}, {square})\n"
            f"               by IntegerMod.make_equal_of_difference_multiple(multiple := {multiple});\n"
            "        done\n"
            "      }"
        )
        arms.append(f"done by {inject(squares.index(square), len(squares), chain)}")
    tree = case_tree(values, arms, "xValue", 2)
    value_goal = disjunction(values, "\n      ∨ ")
    return f"""theorem IntegerMod.square_mod_{word} (x : IntegerMod({modulus}))
        : {goal} := {{
  {value_goal}
      by IntegerMod.mod_{word}_cases(x);
  {tree}
}}
"""


def square_zero_forces_zero(modulus: int) -> str:
    """Sound only at a prime modulus: r² ≡ 0 has the single root r ≡ 0."""
    word = WORDS[modulus]
    values = [f"x = IntegerMod.residue({modulus}, {value})"
              for value in range(modulus)]
    arms = []
    for value in range(modulus):
        if value == 0:
            arms.append("done by xValue")
            continue
        square = (value * value) % modulus
        multiple = (value * value - square) // modulus
        arms.append(
            "{\n"
            f"        IntegerMod.residue({modulus}, 0) ≠ IntegerMod.residue({modulus}, {square})\n"
            f"            by IntegerMod.residue_distinct_below_modulus("
            f"{modulus}, 0, {square}, done, done, done)\n"
            "            as classesDistinct;\n"
            f"        IntegerMod.residue({modulus}, 0)\n"
            "           = x * x by Equality.symmetry(squareZero)\n"
            f"           = IntegerMod.residue({modulus}, {value})"
            f" * IntegerMod.residue({modulus}, {value}) by substituting xValue\n"
            f"           = IntegerMod.residue({modulus}, {square})\n"
            f"               by IntegerMod.make_equal_of_difference_multiple(multiple := {multiple})\n"
            "        as classesEqual;\n"
            "        False by classesDistinct(classesEqual) as impossible;\n"
            f"        done by False.eliminate_proposition("
            f"x = IntegerMod.residue({modulus}, 0), impossible)\n"
            "      }"
        )
    tree = case_tree(values, arms, "xValue", 2)
    value_goal = disjunction(values, "\n      ∨ ")
    return f"""theorem IntegerMod.square_zero_mod_{word}_forces_zero (x : IntegerMod({modulus}))
        (squareZero : x * x = IntegerMod.residue({modulus}, 0))
        : x = IntegerMod.residue({modulus}, 0) := {{
  {value_goal}
      by IntegerMod.mod_{word}_cases(x);
  {tree}
}}
"""


def modulus_block(modulus: int, positive_lemma: str | None,
                  ladder_from: int | None, prime: bool) -> str:
    parts = [below_values(modulus, positive_lemma, ladder_from),
             mod_cases(modulus),
             square_mod(modulus)]
    if prime:
        parts.append(square_zero_forces_zero(modulus))
    return "\n".join(parts)


# ----------------------------------------------------------------------
# Residue facts about a diagonal form, enumerated over square classes.

def scaled(modulus: int, coefficient: int, atom: str) -> str:
    """Coefficients are spelled as classes of integer literals, so a consumer
    holding an ordinary integer equation can chain into these statements."""
    if coefficient == 1:
        return atom
    return f"IntegerMod.make({modulus}, ({coefficient} : ℤ)) * ({atom})"


def form_at(modulus: int, coefficients: list[int], chosen: list[int],
            upto: int) -> str:
    """The form with the first `upto + 1` squares replaced by their classes."""
    terms = []
    for index, coefficient in enumerate(coefficients):
        variable = VARIABLES[index]
        atom = (f"IntegerMod.residue({modulus}, {chosen[index]})"
                if index <= upto else f"{variable} * {variable}")
        terms.append(scaled(modulus, coefficient, atom))
    return " + ".join(terms)


def residue_chain(modulus: int, coefficients: list[int], chosen: list[int],
                  target: int) -> tuple[str, int]:
    """Chain the target class down to the class the chosen squares produce."""
    total = sum(coefficient * square
                for coefficient, square in zip(coefficients, chosen))
    remainder = total % modulus
    multiple = (total - remainder) // modulus
    steps = [f"        IntegerMod.residue({modulus}, {target})",
             "           = " + form_at(modulus, coefficients, chosen, -1)
             + " by Equality.symmetry(formValue)"]
    for index in range(len(coefficients)):
        steps.append(
            "           = " + form_at(modulus, coefficients, chosen, index)
            + f" by substituting {VARIABLES[index]}Square")
    steps.append(f"           = IntegerMod.residue({modulus}, {remainder})\n"
                 "               by IntegerMod.make_equal_of_difference_multiple("
                 f"multiple := {multiple})\n"
                 "        as classesEqual;")
    return "\n".join(steps), remainder


def contradiction_arm(modulus: int, coefficients: list[int],
                      chosen: list[int], target: int, goal: str) -> str:
    chain, remainder = residue_chain(modulus, coefficients, chosen, target)
    assert remainder != target, (modulus, coefficients, chosen, target)
    closing = ("        done by classesDistinct(classesEqual)" if goal == "False"
               else "        False by classesDistinct(classesEqual) as impossible;\n"
                    f"        done by False.eliminate_proposition({goal}, impossible)")
    return (
        "{\n"
        f"        IntegerMod.residue({modulus}, {target})"
        f" ≠ IntegerMod.residue({modulus}, {remainder})\n"
        f"            by IntegerMod.residue_distinct_below_modulus("
        f"{modulus}, {target}, {remainder}, done, done, done)\n"
        "            as classesDistinct;\n"
        + chain + "\n"
        + closing + "\n"
        "      }"
    )


def form_fact(modulus: int, coefficients: list[int], target: int,
              name: str) -> str:
    """What the square classes say about the form meeting the target class.

    With no surviving assignment the statement is `False`.  Otherwise it
    reports, per variable, which square classes survive — the projection of
    the surviving assignments, which is all a descent consumer needs and is
    far easier to read than the assignments themselves.
    """
    word = WORDS[modulus]
    squares = square_classes(modulus)
    variables = VARIABLES[:len(coefficients)]

    survivors = [
        list(assignment)
        for assignment in product(squares, repeat=len(coefficients))
        if sum(coefficient * square
               for coefficient, square in zip(coefficients, assignment))
        % modulus == target
    ]
    projections = [sorted({assignment[index] for assignment in survivors})
                   for index in range(len(coefficients))]

    def conjunct(index: int) -> str:
        variable = variables[index]
        return disjunction(
            [f"{variable} * {variable} = IntegerMod.residue({modulus}, {square})"
             for square in projections[index]], " ∨ ")

    if survivors:
        goal = " ∧ ".join(
            conjunct(index) if len(projections[index]) == 1
            else f"({conjunct(index)})" for index in range(len(coefficients)))
    else:
        goal = "False"

    def surviving_arm(chosen: list[int]) -> str:
        proof = inject(projections[-1].index(chosen[-1]), len(projections[-1]),
                       f"{variables[-1]}Square")
        for index in reversed(range(len(variables) - 1)):
            inner = inject(projections[index].index(chosen[index]),
                           len(projections[index]), f"{variables[index]}Square")
            proof = f"And.introduction({inner}, {proof})"
        return f"done by {proof}"

    def build(depth: int, chosen: list[int]) -> str:
        if depth == len(coefficients):
            if chosen in survivors:
                return surviving_arm(chosen)
            return contradiction_arm(modulus, coefficients, chosen, target, goal)
        variable = variables[depth]
        values = [f"{variable} * {variable} = IntegerMod.residue({modulus}, {square})"
                  for square in squares]
        arms = [build(depth + 1, chosen + [square]) for square in squares]
        tree = case_tree(values, arms, f"{variable}Square", 4 + 2 * depth)
        return tree if depth == 0 else "{\n      " + tree + "\n    }"

    setup = "\n".join(
        "  " + disjunction(
            [f"{variable} * {variable} = IntegerMod.residue({modulus}, {square})"
             for square in squares], "\n      ∨ ")
        + f"\n      by IntegerMod.square_mod_{word}({variable});"
        for variable in variables)
    form = " + ".join(
        scaled(modulus, coefficient, f"{VARIABLES[index]} * {VARIABLES[index]}")
        for index, coefficient in enumerate(coefficients))
    return f"""theorem IntegerMod.{name} ({" ".join(variables)} : IntegerMod({modulus}))
        (formValue : {form} = IntegerMod.residue({modulus}, {target}))
        : {goal} := {{
{setup}
  {build(0, [])}
}}
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    sections = [
        modulus_block(5, "Natural.positive_below_five", None, True),
        modulus_block(7, "Natural.positive_below_seven", None, True),
        below_values(14, "Natural.positive_below_fourteen", None),
        below_values(15, None, 14),
        modulus_block(16, None, 15, False),
        form_fact(5, [1], 3, "square_not_three_mod_five"),
        form_fact(5, [1, 2], 0,
                  "square_plus_double_square_zero_mod_five_classes"),
        form_fact(7, [2, 1], 0,
                  "double_square_plus_square_zero_mod_seven_classes"),
        form_fact(16, [1, 2, 3], 8,
                  "square_plus_double_plus_triple_square_eight_mod_sixteen_classes"),
        form_fact(16, [1, 2, 3], 10,
                  "square_plus_double_plus_triple_square_not_ten_mod_sixteen"),
    ]

    header = """-- Generated by scripts/generate_residue_arithmetic.py. Do not edit.
--
-- Residue and square-class arithmetic at the moduli the rank-three
-- exclusion descents need: 5, 7 and 16.

module Algebra.residue_arithmetic_generated

import Algebra.three_squares_mod_eight
import Natural.multiply_bounds

"""
    output = ROOT / "library/Algebra/residue_arithmetic_generated.math"
    expected = header + "\n".join(sections)
    if args.check:
        if not output.exists() or output.read_text() != expected:
            print(f"stale generated file: {output}")
            return 1
        print("residue-arithmetic-generated-check: PASS")
        return 0
    if not output.exists() or output.read_text() != expected:
        output.write_text(expected)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

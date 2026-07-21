#!/usr/bin/env python3
"""Classify the rank-four escalation normal forms up to integral isometry.

This is an untrusted discovery tool.  It reconstructs the concrete Gram
matrices named by the checked rank-four classifiers, partitions them by exact
theta-series prefixes, and then searches for a unimodular change of basis.
Every positive result intended for the library must still be emitted as a
certificate and checked by the kernel.

The isometry search itself is exhaustive.  If ``U^T B U = A``, column ``i``
of ``U`` has ``B``-norm ``A[i,i]``.  Positive definiteness and

    x_i^2 <= (x^T B x) (B^-1)[i,i]

give a finite, exact coordinate box containing every possible column.  The
search enumerates all vectors in those boxes and all compatible bases.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import lru_cache
from itertools import permutations, product
from math import isqrt
from pathlib import Path
import sys
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from generate_rank_four_diagonal_branch import (  # noqa: E402
    BRANCHES as DIAGONAL_BRANCHES,
    normal_forms as diagonal_normal_forms,
)
from generate_rank_four_odd_diagonal_branches import (  # noqa: E402
    BRANCHES as ODD_BRANCHES,
    normal_forms as odd_normal_forms,
)
from generate_rank_four_pilot import REPRESENTATIVES as PILOT_REPRESENTATIVES  # noqa: E402
from generate_rank_four_weighted_diagonal_branches import (  # noqa: E402
    BRANCHES as WEIGHTED_BRANCHES,
    normal_forms as weighted_normal_forms,
)


Vector = tuple[int, int, int, int]
Matrix = tuple[
    tuple[int, int, int, int],
    tuple[int, int, int, int],
    tuple[int, int, int, int],
    tuple[int, int, int, int],
]

EXPECTED_INPUT_COUNT = 276
EXPECTED_CLASS_COUNT = 207
EXPECTED_IDENTIFICATION_COUNT = 69


@dataclass(frozen=True)
class NamedForm:
    name: str
    family: str
    parameters: tuple[int, ...]
    matrix: Matrix


@dataclass(frozen=True)
class Identification:
    source: NamedForm
    representative: NamedForm
    change_of_basis: Matrix


def determinant(matrix: tuple[tuple[int, ...], ...]) -> int:
    """Compute a small determinant by the Leibniz formula."""
    size = len(matrix)
    total = 0
    for permutation in permutations(range(size)):
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(size)
            for j in range(i + 1, size)
        )
        term = -1 if inversions % 2 else 1
        for row, column in enumerate(permutation):
            term *= matrix[row][column]
        total += term
    return total


def bordered(parent: tuple[tuple[int, int, int], ...], border: tuple[int, int, int], corner: int) -> Matrix:
    return tuple(
        tuple(parent[i][j] if i < 3 and j < 3 else border[i] if i < 3 else border[j] if j < 3 else corner for j in range(4))
        for i in range(4)
    )  # type: ignore[return-value]


def diagonal_parent(a: int, b: int, c: int) -> tuple[tuple[int, int, int], ...]:
    return ((a, 0, 0), (0, b, 0), (0, 0, c))


def named_forms() -> list[NamedForm]:
    forms: list[NamedForm] = []

    for norm, border in PILOT_REPRESENTATIVES.items():
        forms.append(NamedForm(f"pilot.norm{norm}", "pilot", (norm, *border), bordered(diagonal_parent(1, 1, 1), border, 7)))

    for residue in (0, 1):
        for corner in range(1, 7):
            forms.append(
                NamedForm(
                    f"triple.r{residue}.c{corner}",
                    "triple",
                    (residue, corner),
                    bordered(diagonal_parent(1, 1, 3), (0, 0, residue), corner),
                )
            )

    for residue, corner in diagonal_normal_forms(DIAGONAL_BRANCHES["double"]):
        forms.append(
            NamedForm(
                f"double.r{residue}.c{corner}",
                "double",
                (residue, corner),
                bordered(diagonal_parent(1, 1, 2), (0, 0, residue), corner),
            )
        )

    for key, branch in WEIGHTED_BRANCHES.items():
        if key == "d1":
            continue  # Proven aliases of the double branch.
        for second, third, corner in weighted_normal_forms(branch):
            forms.append(
                NamedForm(
                    f"weighted.{key}.s{second}.r{third}.c{corner}",
                    f"weighted.{key}",
                    (second, third, corner),
                    bordered(diagonal_parent(1, 2, branch.d), (0, second, third), corner),
                )
            )

    for key, branch in ODD_BRANCHES.items():
        parent = ((1, 0, 0), (0, 2, 1), (0, 1, branch.form_corner))
        for residue, corner in odd_normal_forms(branch):
            forms.append(
                NamedForm(
                    f"odd.{key}.r{residue}.c{corner}",
                    f"odd.{key}",
                    (residue, corner),
                    bordered(parent, (0, residue, 0), corner),
                )
            )

    assert len(forms) == EXPECTED_INPUT_COUNT
    assert len({form.name for form in forms}) == len(forms)
    assert all(determinant(form.matrix) > 0 for form in forms)
    return forms


def principal_cofactor(matrix: Matrix, index: int) -> int:
    minor = tuple(tuple(value for j, value in enumerate(row) if j != index) for i, row in enumerate(matrix) if i != index)
    return determinant(minor)


def coordinate_bounds(matrix: Matrix, maximum_norm: int) -> tuple[int, int, int, int]:
    det = determinant(matrix)
    assert det > 0
    bounds = tuple(isqrt(maximum_norm * principal_cofactor(matrix, i) // det) for i in range(4))
    return bounds  # type: ignore[return-value]


def bilinear(matrix: Matrix, left: Vector, right: Vector) -> int:
    return sum(left[i] * matrix[i][j] * right[j] for i in range(4) for j in range(4))


@lru_cache(maxsize=None)
def vectors_by_norm(matrix: Matrix, maximum_norm: int) -> tuple[tuple[Vector, ...], ...]:
    by_norm: list[list[Vector]] = [[] for _ in range(maximum_norm + 1)]
    bounds = coordinate_bounds(matrix, maximum_norm)
    for vector in product(*(range(-bound, bound + 1) for bound in bounds)):
        norm = bilinear(matrix, vector, vector)  # type: ignore[arg-type]
        if 0 <= norm <= maximum_norm:
            by_norm[norm].append(vector)  # type: ignore[arg-type]
    return tuple(tuple(vectors) for vectors in by_norm)


def theta_prefix(matrix: Matrix, limit: int) -> tuple[int, ...]:
    return tuple(len(vectors) for vectors in vectors_by_norm(matrix, limit))


def columns_to_matrix(columns: list[Vector]) -> Matrix:
    return tuple(tuple(columns[j][i] for j in range(4)) for i in range(4))  # type: ignore[return-value]


def multiply(left: Matrix, right: Matrix) -> Matrix:
    return tuple(
        tuple(sum(left[i][k] * right[k][j] for k in range(4)) for j in range(4))
        for i in range(4)
    )  # type: ignore[return-value]


def inverse_unimodular(matrix: Matrix) -> Matrix:
    det = determinant(matrix)
    assert abs(det) == 1

    def cofactor(row: int, column: int) -> int:
        minor = tuple(
            tuple(value for j, value in enumerate(source_row) if j != column)
            for i, source_row in enumerate(matrix)
            if i != row
        )
        return (-1 if (row + column) % 2 else 1) * determinant(minor)

    inverse = tuple(tuple(cofactor(j, i) // det for j in range(4)) for i in range(4))
    identity: Matrix = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
    assert multiply(matrix, inverse) == identity
    assert multiply(inverse, matrix) == identity
    return inverse  # type: ignore[return-value]


def find_isometry(target: Matrix, source: Matrix) -> Matrix | None:
    """Find ``U`` with ``U^T source U = target``, or exhaust all such ``U``."""
    maximum_norm = max(target[i][i] for i in range(4))
    source_vectors = vectors_by_norm(source, maximum_norm)
    order = sorted(range(4), key=lambda i: len(source_vectors[target[i][i]]))
    chosen: dict[int, Vector] = {}

    def search(depth: int) -> Matrix | None:
        if depth == 4:
            columns = [chosen[i] for i in range(4)]
            change = columns_to_matrix(columns)
            return change if abs(determinant(change)) == 1 else None

        index = order[depth]
        for vector in source_vectors[target[index][index]]:
            if depth == 0:
                first_nonzero = next((entry for entry in vector if entry != 0), 0)
                if first_nonzero < 0:
                    continue
            if all(bilinear(source, chosen[other], vector) == target[other][index] for other in chosen):
                chosen[index] = vector
                result = search(depth + 1)
                if result is not None:
                    return result
                del chosen[index]
        return None

    return search(0)


def classify(forms: Iterable[NamedForm], theta_limit: int) -> tuple[list[NamedForm], list[Identification]]:
    buckets: dict[tuple[int, tuple[int, ...]], list[NamedForm]] = {}
    for form in forms:
        invariant = determinant(form.matrix), theta_prefix(form.matrix, theta_limit)
        buckets.setdefault(invariant, []).append(form)

    representatives: list[NamedForm] = []
    identifications: list[Identification] = []
    for bucket in buckets.values():
        bucket_representatives: list[NamedForm] = []
        for form in bucket:
            for representative in bucket_representatives:
                change = find_isometry(representative.matrix, form.matrix)
                if change is not None:
                    identifications.append(Identification(form, representative, change))
                    break
            else:
                bucket_representatives.append(form)
                representatives.append(form)
    return representatives, identifications


def format_matrix(matrix: Matrix) -> str:
    return "[" + ", ".join("[" + ", ".join(map(str, row)) + "]" for row in matrix) + "]"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--theta-limit", type=int, default=15)
    parser.add_argument("--show-witnesses", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    forms = named_forms()
    representatives, identifications = classify(forms, args.theta_limit)
    if args.check and (
        len(forms) != EXPECTED_INPUT_COUNT
        or len(representatives) != EXPECTED_CLASS_COUNT
        or len(identifications) != EXPECTED_IDENTIFICATION_COUNT
    ):
        print(
            "rank-four classification changed: "
            f"{len(forms)} inputs, {len(representatives)} classes, "
            f"{len(identifications)} identifications",
            file=sys.stderr,
        )
        return 1
    family_counts: dict[str, int] = {}
    for representative in representatives:
        family_counts[representative.family] = family_counts.get(representative.family, 0) + 1

    print(f"input normal forms: {len(forms)}")
    print(f"integral-isometry classes: {len(representatives)}")
    print(f"duplicate normal forms: {len(identifications)}")
    print("chosen representatives by family:")
    for family, count in family_counts.items():
        print(f"  {family}: {count}")
    if args.show_witnesses:
        print("identifications:")
        for identification in identifications:
            print(f"  {identification.source.name} -> {identification.representative.name}")
            print(f"    U = {format_matrix(identification.change_of_basis)}")
    if args.check:
        print("rank-four-isometry-classification-check: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

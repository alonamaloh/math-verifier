#!/usr/bin/env node

// Reproduce every finite calculation used in PROOF_15_THEOREM_REMAINING.md.
//
// The script uses only exact integer arithmetic.  All numbers involved are far
// below Number.MAX_SAFE_INTEGER.  It verifies:
//
//   * the CRT residual covers modulo lcm(12, 49) = 588;
//   * the orthogonal vectors and their norms;
//   * the alternative ternary section of Q_{1,7}; and
//   * direct representability of every target in each finite prefix.

"use strict";

const assert = require("node:assert/strict");

const mod = (value, modulus) => ((value % modulus) + modulus) % modulus;

function safe7(value) {
  const residue49 = mod(value, 49);
  const safeAt7 =
    residue49 % 7 !== 0 || residue49 === 7 || residue49 === 14 || residue49 === 28;
  const residue12 = mod(value, 12);
  return safeAt7 && residue12 !== 7 && residue12 !== 10;
}

const residualCases = [
  { m: 7, choices: [1, 2, 3, 4, 6], expected: [100, 10, 5, 1, 1] },
  { m: 266, choices: [1, 2, 3, 4, 5, 6], expected: [94, 9, 10, 1, 2, 1] },
  { m: 280, choices: [1, 2, 3, 4, 6, 9], expected: [93, 9, 7, 4, 2, 2] },
  { m: 329, choices: [1, 2, 3, 4, 6, 9], expected: [94, 9, 9, 2, 1, 2] },
  { m: 238, choices: [1, 2, 3, 4, 5, 6], expected: [94, 9, 10, 1, 2, 1] },
  { m: 287, choices: [1, 2, 3, 4, 6, 9], expected: [93, 9, 8, 3, 2, 2] },
];

function checkResidualCover({ m, choices, expected }, oddOnly = false) {
  const firstSolvedCounts = Array(choices.length).fill(0);
  let sourceCount = 0;

  for (let source = 0; source < 588; source += 1) {
    // Every least exception is squarefree.  The first two tests are exactly
    // the consequences of squarefreeness visible modulo 588.
    if (source % 4 === 0 || source % 49 === 0) continue;
    if (oddOnly && source % 2 === 0) continue;
    if (safe7(source)) continue;

    sourceCount += 1;
    const firstChoice = choices.findIndex((t) => safe7(source - m * t * t));
    assert.notEqual(
      firstChoice,
      -1,
      `no residual choice works for m=${m}, source=${source} (mod 588)`,
    );
    firstSolvedCounts[firstChoice] += 1;
  }

  assert.deepEqual(firstSolvedCounts, expected);
  return { sourceCount, firstSolvedCounts };
}

function dot(gram, left, right) {
  let value = 0;
  for (let i = 0; i < left.length; i += 1) {
    for (let j = 0; j < right.length; j += 1) {
      value += left[i] * gram[i][j] * right[j];
    }
  }
  return value;
}

function qGram(r, c) {
  return [
    [1, 0, 0, 0],
    [0, 2, 1, r],
    [0, 1, 4, 0],
    [0, r, 0, c],
  ];
}

const standardBasis4 = [
  [1, 0, 0, 0],
  [0, 1, 0, 0],
  [0, 0, 1, 0],
  [0, 0, 0, 1],
];

const finiteCases = [
  { r: 0, c: 7, bound: 252, expectedTriples: 2387 },
  { r: 1, c: 6, bound: 9576, expectedTriples: 636475 },
  { r: 2, c: 8, bound: 22680, expectedTriples: 2262013 },
  { r: 2, c: 9, bound: 26649, expectedTriples: 2657751 },
  { r: 3, c: 10, bound: 8568, expectedTriples: 569451 },
  { r: 3, c: 11, bound: 23247, expectedTriples: 2318499 },
  { r: 1, c: 7, bound: 11340, expectedTriples: 753905 },
];

function floorSqrt(value) {
  assert(Number.isSafeInteger(value) && value >= 0);
  let low = 0;
  let high = value + 1;
  while (low + 1 < high) {
    const middle = Math.floor((low + high) / 2);
    if (middle * middle <= value) low = middle;
    else high = middle;
  }
  return low;
}

function floorDivideNonnegative(numerator, denominator) {
  assert(Number.isSafeInteger(numerator) && numerator >= 0);
  assert(Number.isSafeInteger(denominator) && denominator > 0);
  let quotient = Math.floor(numerator / denominator);
  while ((quotient + 1) * denominator <= numerator) quotient += 1;
  while (quotient * denominator > numerator) quotient -= 1;
  return quotient;
}

function checkFinitePrefix({ r, c, bound, expectedTriples }) {
  const determinantFactor = 7 * c - 4 * r * r;
  assert(determinantFactor > 0);

  // These deliberately rounded-outward global bounds are followed by the
  // exact inequalities inside the loops.
  const wLimit = floorSqrt(floorDivideNonnegative(7 * bound, determinantFactor)) + 1;
  const shiftedZLimit = floorSqrt(14 * bound) + 2;
  const shiftedYLimit = floorSqrt(2 * bound) + 2;

  const firstTripleForH = Array(bound + 1).fill(null);
  let admissibleTriples = 0;

  for (let w = -wLimit; w <= wLimit; w += 1) {
    const zLow = Math.ceil((r * w - shiftedZLimit) / 7);
    const zHigh = Math.floor((r * w + shiftedZLimit) / 7);
    for (let z = zLow; z <= zHigh; z += 1) {
      const yLow = Math.ceil((-shiftedYLimit - z - r * w) / 2);
      const yHigh = Math.floor((shiftedYLimit - z - r * w) / 2);
      for (let y = yLow; y <= yHigh; y += 1) {
        const h =
          2 * y * y + 2 * y * z + 4 * z * z + 2 * r * y * w + c * w * w;
        if (h < 0 || h > bound) continue;
        admissibleTriples += 1;
        if (firstTripleForH[h] === null) firstTripleForH[h] = [y, z, w];
      }
    }
  }

  assert.equal(admissibleTriples, expectedTriples);

  const witness = Array(bound + 1).fill(null);
  for (let h = 0; h <= bound; h += 1) {
    if (firstTripleForH[h] === null) continue;
    for (let x = 0; h + x * x <= bound; x += 1) {
      const target = h + x * x;
      if (witness[target] === null) witness[target] = [x, ...firstTripleForH[h]];
    }
  }

  for (let target = 1; target <= bound; target += 1) {
    assert.notEqual(witness[target], null, `Q_{${r},${c}} misses ${target}`);
    const [x, y, z, w] = witness[target];
    const value =
      x * x +
      2 * y * y +
      2 * y * z +
      4 * z * z +
      2 * r * y * w +
      c * w * w;
    assert.equal(value, target);
  }

  return { admissibleTriples, missingTargets: 0 };
}

console.log("CRT residual covers");
for (const residualCase of residualCases) {
  const result = checkResidualCover(residualCase);
  console.log(
    `  m=${residualCase.m}: sources=${result.sourceCount}, first-solved=${result.firstSolvedCounts.join(",")}`,
  );
}
const odd315 = checkResidualCover(
  { m: 315, choices: [1, 2, 3, 4, 5, 6], expected: [48, 5, 6, 1, 2, 1] },
  true,
);
console.log(`  m=315 (odd sources): sources=${odd315.sourceCount}, first-solved=${odd315.firstSolvedCounts.join(",")}`);

console.log("Orthogonal complements");
for (const { r, c } of finiteCases) {
  const gram = qGram(r, c);
  const vector = r === 0 ? standardBasis4[3] : [0, -4 * r, r, 7];
  for (let i = 0; i < 3; i += 1) assert.equal(dot(gram, vector, standardBasis4[i]), 0);
  const expectedNorm = r === 0 ? c : 49 * c - 28 * r * r;
  assert.equal(dot(gram, vector, vector), expectedNorm);
  console.log(`  Q_{${r},${c}}: norm=${expectedNorm}`);
}

console.log("Alternative section of Q_{1,7}");
{
  const gram = qGram(1, 7);
  const basis = [
    [0, 1, 0, 0],
    [2, 0, 0, 0],
    [1, 1, -1, -1],
  ];
  const expectedGram = [
    [2, 0, 0],
    [0, 4, 2],
    [0, 2, 10],
  ];
  for (let i = 0; i < 3; i += 1) {
    for (let j = 0; j < 3; j += 1) {
      assert.equal(dot(gram, basis[i], basis[j]), expectedGram[i][j]);
    }
  }
  const orthogonal = [0, 1, -4, 2];
  for (const vector of basis) assert.equal(dot(gram, orthogonal, vector), 0);
  assert.equal(dot(gram, orthogonal, orthogonal), 90);
  console.log("  Gram matrix and norm-90 orthogonal vector verified");
}

console.log("Finite quaternary prefixes");
for (const finiteCase of finiteCases) {
  const result = checkFinitePrefix(finiteCase);
  const label = `Q_{${finiteCase.r},${finiteCase.c}} through ${finiteCase.bound}`;
  console.log(`  ${label}: triples=${result.admissibleTriples}, missing=${result.missingTargets}`);
}

console.log("All determinant-seven human-proof checks passed.");

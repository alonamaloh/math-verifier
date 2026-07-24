#!/usr/bin/env node

// Reproduce the finite calculations in
// PROOF_REMAINING_TERNARY_CONVERSES.md and
// PROOF_FIFTEEN_THEOREM_ASSEMBLY.md.
//
// This script has no package dependencies. It is a certificate generator
// and drift check, not part of the trusted proof kernel.

"use strict";

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function sameArray(left, right) {
  return left.length === right.length && left.every((value, index) => value === right[index]);
}

function range(stop) {
  return Array.from({ length: stop }, (_, index) => index);
}

function v2(value) {
  assert(value !== 0, "v2 called on zero");
  let n = Math.abs(value);
  let valuation = 0;
  while (n % 2 === 0) {
    n /= 2;
    valuation += 1;
  }
  return valuation;
}

const ternaryForms = {
  q111: [1, 1, 1],
  q123: [1, 2, 3],
  q126: [1, 2, 6],
  q136: [1, 3, 6],
  q236: [2, 3, 6],
  q125: [1, 2, 5],
};

function ternaryValue(coefficients, vector) {
  return coefficients.reduce((total, coefficient, index) =>
    total + coefficient * vector[index] * vector[index], 0);
}

function residueSet(coefficients, modulus) {
  const values = new Set();
  for (const x of range(modulus)) {
    for (const y of range(modulus)) {
      for (const z of range(modulus)) {
        values.add(ternaryValue(coefficients, [x, y, z]) % modulus);
      }
    }
  }
  return values;
}

const expectedMissingMod16 = {
  q111: [7, 15],
  q123: [10],
  q126: [5, 13],
  q136: [14],
  q236: [7, 15],
  q125: [],
};

for (const [name, coefficients] of Object.entries(ternaryForms)) {
  const represented = residueSet(coefficients, 16);
  const missing = range(16).filter(residue => !represented.has(residue));
  assert(sameArray(missing, expectedMissingMod16[name]),
    `${name}: wrong missing residues mod 16: ${missing}`);
}

function parseWitnesses(source) {
  const result = new Map();
  for (const entry of source.trim().split(/\s*;\s*/)) {
    const [residueText, vectorText] = entry.split(":");
    result.set(Number(residueText), vectorText.split(",").map(Number));
  }
  return result;
}

const residueWitnesses = {
  q111: parseWitnesses(
    "1:0,0,1;2:0,1,1;3:1,1,1;5:0,1,2;6:1,1,2;9:0,0,3;10:0,1,3;11:1,1,3;" +
    "13:0,2,3;14:1,2,3;17:0,1,4;18:0,3,3;19:1,3,3;21:1,2,4;22:2,3,3;" +
    "25:0,0,5;26:0,1,5;27:1,1,5;29:0,2,5;30:1,2,5"),
  q123: parseWitnesses(
    "1:1,0,0;2:0,1,0;3:0,0,1;5:0,1,1;6:1,1,1;7:2,0,1;9:1,2,0;11:0,0,5;" +
    "13:0,1,5;14:0,1,2;15:1,1,2;17:1,0,4;18:0,1,4;19:0,0,7;21:0,1,7;" +
    "22:1,1,7;23:2,0,7;25:1,2,4;27:0,0,3;29:0,1,3;30:0,3,2;31:1,3,2"),
  q126: parseWitnesses(
    "1:1,0,0;2:0,1,0;3:1,1,0;6:0,0,1;7:1,0,1;9:1,1,1;10:0,3,2;11:1,3,2;" +
    "14:0,2,1;15:1,2,1;17:3,1,1;18:0,3,0;19:1,3,0;22:0,0,3;23:1,0,3;" +
    "25:1,0,2;26:0,1,2;27:1,1,2;30:0,2,3;31:1,2,3"),
  q136: parseWitnesses(
    "1:1,0,0;2:1,3,1;3:0,1,0;5:1,2,2;6:0,0,1;7:1,0,1;9:0,1,1;10:1,1,1;" +
    "11:0,5,0;13:1,2,0;15:3,0,1;17:1,4,0;18:3,1,1;19:1,2,1;21:3,2,0;" +
    "22:0,0,3;23:1,0,3;25:1,0,2;26:1,1,3;27:0,1,2;29:2,1,3;31:2,1,2"),
  q236: parseWitnesses(
    "1:0,3,1;2:1,0,0;3:0,1,0;5:1,1,0;6:0,0,1;9:0,1,1;10:3,0,2;11:1,1,1;" +
    "13:3,1,2;14:1,2,0;17:2,1,1;18:0,2,1;19:0,3,2;21:3,1,0;22:0,0,3;" +
    "25:0,1,3;26:1,0,2;27:0,1,2;29:1,1,2;30:2,0,3"),
  q125: parseWitnesses(
    "0:1,1,5;1:1,0,0;2:0,1,0;3:1,1,0;4:2,0,0;5:0,0,1;6:0,3,2;7:0,1,1;" +
    "8:1,1,1;9:1,2,0;10:2,3,2;11:2,1,1;12:2,2,0;13:0,0,3;14:1,0,3;" +
    "15:0,1,3;16:1,1,3;17:1,0,4;18:0,1,4;19:1,1,4;20:0,0,2;21:0,0,7;" +
    "22:0,1,2;23:0,1,7;24:1,1,7;25:1,2,4;26:2,1,2;27:2,1,7;28:0,2,2;" +
    "29:0,0,5;30:1,0,5;31:0,1,5"),
};

for (const [name, witnesses] of Object.entries(residueWitnesses)) {
  const coefficients = ternaryForms[name];
  const expectedResidues = name === "q125"
    ? range(32)
    : range(32).filter(residue =>
      residue % 4 !== 0 && !expectedMissingMod16[name].includes(residue % 16));
  assert(sameArray([...witnesses.keys()], expectedResidues),
    `${name}: the mod-32 witness table has the wrong domain`);
  for (const [residue, vector] of witnesses) {
    const actual = ((ternaryValue(coefficients, vector) % 32) + 32) % 32;
    assert(actual === residue, `${name}: bad witness for residue ${residue}`);
    const derivativeValuations = vector
      .map((coordinate, index) => 2 * coefficients[index] * coordinate)
      .filter(value => value !== 0)
      .map(v2);
    assert(derivativeValuations.length > 0 && Math.min(...derivativeValuations) <= 2,
      `${name}: residue ${residue} has no derivative of valuation at most two`);
  }
}

const binaryOneTwoMod3 = new Set();
for (const x of range(3)) for (const y of range(3)) binaryOneTwoMod3.add((x * x + 2 * y * y) % 3);
assert(sameArray([...binaryOneTwoMod3].sort(), [0, 1, 2]), "x^2+2y^2 is not universal mod 3");
assert(sameArray([...residueSet(ternaryForms.q136, 3)].sort(), [0, 1]),
  "q136 has the wrong mod-3 image");
assert(sameArray([...residueSet(ternaryForms.q236, 3)].sort(), [0, 2]),
  "q236 has the wrong mod-3 image");

for (const x of range(5)) {
  for (const y of range(5)) {
    if ((x * x + 2 * y * y) % 5 === 0) {
      assert(x === 0 && y === 0, "x^2+2y^2 is not anisotropic mod 5");
    }
  }
}

function transpose(matrix) {
  return matrix[0].map((_, column) => matrix.map(row => row[column]));
}

function multiplyMatrices(left, right) {
  return left.map(row => right[0].map((_, column) =>
    row.reduce((sum, value, index) => sum + value * right[index][column], 0)));
}

function sameMatrix(left, right) {
  return left.length === right.length &&
    left.every((row, index) => sameArray(row, right[index]));
}

function determinant4(matrix) {
  let result = 0;
  for (const a of range(4)) for (const b of range(4)) for (const c of range(4)) for (const d of range(4)) {
    const permutation = [a, b, c, d];
    if (new Set(permutation).size !== 4) continue;
    let inversions = 0;
    for (let i = 0; i < 4; i += 1) {
      for (let j = i + 1; j < 4; j += 1) {
        if (permutation[i] > permutation[j]) inversions += 1;
      }
    }
    const product = permutation.reduce((value, column, row) => value * matrix[row][column], 1);
    result += inversions % 2 === 0 ? product : -product;
  }
  return result;
}

const B1 = [[1, 0, 0, 0], [0, 2, 0, 1], [0, 0, 3, 0], [0, 1, 0, 4]];
const B2 = [[1, 0, 0, 0], [0, 2, 1, 0], [0, 1, 4, 1], [0, 0, 1, 5]];
const Q1 = [[1, 0, 0, 0], [0, 2, 1, 0], [0, 1, 4, 0], [0, 0, 0, 3]];
const Q2 = [[1, 0, 0, 0], [0, 2, 1, 2], [0, 1, 4, 0], [0, 2, 0, 7]];
const U1 = [[1, 0, 0, 0], [0, -1, -1, 0], [0, 0, 0, -1], [0, 0, 1, 0]];
const U2 = [[1, 0, 0, 0], [0, -1, -1, -1], [0, 0, 1, 0], [0, 0, 0, -1]];

for (const [source, change, target] of [[B1, U1, Q1], [B2, U2, Q2]]) {
  assert(Math.abs(determinant4(change)) === 1, "change of basis is not unimodular");
  const transformed = multiplyMatrices(multiplyMatrices(transpose(change), source), change);
  assert(sameMatrix(transformed, target), "incorrect integral isometry");
}

function bilinear(matrix, left, right) {
  let result = 0;
  for (const i of range(left.length)) {
    for (const j of range(right.length)) result += left[i] * matrix[i][j] * right[j];
  }
  return result;
}

const hBasis = [[-1, 0, 0, 0], [0, -1, 0, 0], [0, -1, 0, 1]];
const complement = [0, -7, 10, 2];
assert(sameArray(hBasis.map(vector => bilinear(Q2, vector, vector)), [1, 2, 5]),
  "wrong 1,2,5 sublattice norms");
for (const i of range(hBasis.length)) {
  for (let j = i + 1; j < hBasis.length; j += 1) {
    assert(bilinear(Q2, hBasis[i], hBasis[j]) === 0, "1,2,5 basis is not orthogonal");
  }
  assert(bilinear(Q2, hBasis[i], complement) === 0, "norm-330 vector is not orthogonal");
}
assert(bilinear(Q2, complement, complement) === 330, "wrong complementary norm");

function q2Value([x, y, z, w]) {
  return x * x + 2 * y * y + 2 * y * z + 4 * z * z + 4 * y * w + 7 * w * w;
}

function cValue([s, r, c], [x, y, z, w]) {
  return x * x + 2 * y * y + 5 * z * z + 2 * s * y * w + 2 * r * z * w + c * w * w;
}

function missingFromBox(valueFunction, bounds, targets) {
  const targetSet = new Set(targets);
  const represented = new Set();
  const [xBound, yBound, zBound, wBound] = bounds;
  for (let w = -wBound; w <= wBound; w += 1) {
    for (let z = -zBound; z <= zBound; z += 1) {
      for (let y = -yBound; y <= yBound; y += 1) {
        const base = valueFunction([0, y, z, w]);
        for (let x = 0; x <= xBound; x += 1) {
          const value = base + x * x;
          if (targetSet.has(value)) represented.add(value);
        }
      }
    }
  }
  return [...targetSet].filter(value => !represented.has(value)).sort((a, b) => a - b);
}

const q2Targets = [
  ...range(13).map(b => 25 * b + 10),
  ...range(53).map(b => 25 * b + 15),
];
assert(sameArray(missingFromBox(q2Value, [36, 56, 25, 17], q2Targets), [10]),
  "the second truant-10 finite box has the wrong missing set");
assert(q2Value([0, -1, -2, 6]) === 250, "wrong 250 witness");

const tailRows = [
  [[0, 0, 5], 1, 0, 0, 5],
  [[0, 0, 5], 2, 0, 0, 20],
  [[1, 1, 5], 10, 5, 2, 430],
  [[1, 1, 5], 20, 10, 4, 1720],
  [[1, 1, 9], 10, 5, 2, 830],
  [[1, 1, 9], 20, 10, 4, 3320],
  [[1, 2, 8], 20, 10, 8, 2680],
  [[1, 2, 8], 10, 5, 4, 670],
];

for (const [[s, r, c], w, expectedS, expectedT, expectedD] of tailRows) {
  assert(s * w === 2 * expectedS, "wrong y-shift in tail table");
  assert(r * w === 5 * expectedT, "wrong z-shift in tail table");
  assert(c * w * w - 2 * expectedS * expectedS - 5 * expectedT * expectedT === expectedD,
    "wrong correction in tail table");
}

const finiteCases = [
  [[0, 0, 5], [3, 3, 2, 2], [15]],
  [[1, 1, 5], [41, 40, 23, 20],
    [...range(17).map(b => 25 * b + 10), ...range(69).map(b => 25 * b + 15)]],
  [[1, 1, 9], [57, 51, 30, 20],
    [...range(33).map(b => 25 * b + 10), ...range(133).map(b => 25 * b + 15)]],
  [[1, 2, 8], [51, 47, 32, 20],
    [...range(107).map(b => 25 * b + 10), ...range(27).map(b => 25 * b + 15)]],
];

for (const [parameters, bounds, targets] of finiteCases) {
  const missing = missingFromBox(vector => cValue(parameters, vector), bounds, targets);
  assert(sameArray(missing, [15]), `${parameters}: wrong finite missing set ${missing}`);
}

const witnesses375 = [
  [[0, 0, 5], [0, 5, 1, 8]],
  [[1, 1, 5], [0, -1, 7, 4]],
  [[1, 1, 9], [1, 3, -2, 6]],
  [[1, 2, 8], [0, 3, 5, 4]],
];
for (const [parameters, witness] of witnesses375) {
  assert(cValue(parameters, witness) === 375, `${parameters}: wrong 375 witness`);
}

console.log("All remaining-converse and final-assembly finite checks passed.");

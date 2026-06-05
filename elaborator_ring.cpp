// Out-of-line Elaborator method definitions: the `ring` / `field` tactic.
//
// Part of the elaborator split (see elaborator_internal.hpp): the class is
// declared in the header; each elaborator_*.cpp defines a topical slice of
// its methods as `Elaborator::method(...)`. This translation unit holds the
// commutative-ring normalisation tactic (`ring`), the field tactic
// (`field`), the `linear_combination` tactic, and their shared polynomial /
// proof-term machinery.

#include "elaborator_internal.hpp"

// ---- Numerical fast-fail fingerprints (GF(2^64 - 59)) --------------------
//
// Before the expensive symbolic normalise + polynomial-dict comparison,
// `ring`/`field` evaluate both sides at a random-ish point in GF(p) (atoms
// stand in via their subtree hash). If the two fingerprints disagree the
// identity is false and we can bail immediately (Schwartz-Zippel: a false
// polynomial identity collides only with probability ~degree/p).

uint64_t Elaborator::fingerprintAdd(uint64_t leftValue, uint64_t rightValue) const {
    // Both inputs are < p < 2^64, so sum fits in unsigned 64 with
    // at most one wraparound. Reduce mod p with a single conditional.
    uint64_t sum = leftValue + rightValue;
    // Overflow OR sum >= p both want reduction by p.
    if (sum < leftValue || sum >= kFingerprintModulus) {
        sum -= kFingerprintModulus;
    }
    return sum;
}

uint64_t Elaborator::fingerprintSubtract(
    uint64_t leftValue, uint64_t rightValue) const {
    return leftValue >= rightValue
        ? leftValue - rightValue
        : leftValue + (kFingerprintModulus - rightValue);
}

uint64_t Elaborator::fingerprintNegate(uint64_t value) const {
    return value == 0 ? 0 : kFingerprintModulus - value;
}

uint64_t Elaborator::fingerprintMultiply(
    uint64_t leftValue, uint64_t rightValue) const {
    // 64-bit × 64-bit needs 128 bits; rely on the compiler's
    // __int128 (clang / gcc on every platform this project targets).
    return (uint64_t)(((__uint128_t)leftValue
                        * (__uint128_t)rightValue)
                       % (__uint128_t)kFingerprintModulus);
}

uint64_t Elaborator::fingerprintModularPower(
    uint64_t base, uint64_t exponent) const {
    uint64_t result = 1;
    uint64_t current = base % kFingerprintModulus;
    while (exponent > 0) {
        if (exponent & 1ull) {
            result = fingerprintMultiply(result, current);
        }
        current = fingerprintMultiply(current, current);
        exponent >>= 1;
    }
    return result;
}

// Modular inverse via Fermat's little theorem: a^(p-2) mod p.
// Returns nullopt iff a == 0 (no inverse, division by zero).
std::optional<uint64_t> Elaborator::fingerprintModularInverse(uint64_t value) const {
    if (value % kFingerprintModulus == 0) return std::nullopt;
    return fingerprintModularPower(value, kFingerprintModulus - 2);
}

// Recursively evaluate an expression as an element of GF(p), with
// opaque atoms replaced by their cached subtree hash. Returns
// nullopt on division by zero (a `<C>.reciprocal_function` applied
// to something whose fingerprint is 0).
std::optional<uint64_t> Elaborator::evaluateFingerprint(
    ExpressionPointer expression,
    const std::string& carrierName) const {
    const std::string addName       = carrierName + ".add";
    const std::string subtractName  = carrierName + ".subtract";
    const std::string multiplyName  = carrierName + ".multiply";
    const std::string negateName    = carrierName + ".negate";
    const std::string zeroName      = carrierName + ".zero";
    const std::string oneName       = carrierName + ".one";
    const std::string reciprocalName
        = carrierName + ".reciprocal_function";
    // Constants.
    if (auto* head = std::get_if<Constant>(&expression->node)) {
        if (head->name == zeroName) return uint64_t{0};
        if (head->name == oneName) return uint64_t{1};
    }
    // Binary operators (peel two Application layers).
    if (auto* outer = std::get_if<Application>(&expression->node)) {
        if (auto* inner =
                std::get_if<Application>(&outer->function->node)) {
            if (auto* head =
                    std::get_if<Constant>(&inner->function->node)) {
                if (head->name == addName
                    || head->name == subtractName
                    || head->name == multiplyName) {
                    auto leftValue = evaluateFingerprint(
                        inner->argument, carrierName);
                    auto rightValue = evaluateFingerprint(
                        outer->argument, carrierName);
                    if (!leftValue || !rightValue) return std::nullopt;
                    if (head->name == addName) {
                        return fingerprintAdd(*leftValue, *rightValue);
                    }
                    if (head->name == subtractName) {
                        return fingerprintSubtract(
                            *leftValue, *rightValue);
                    }
                    return fingerprintMultiply(*leftValue, *rightValue);
                }
            }
        }
        // Unary operators (one Application layer).
        if (auto* head =
                std::get_if<Constant>(&outer->function->node)) {
            if (head->name == negateName) {
                auto value = evaluateFingerprint(
                    outer->argument, carrierName);
                if (!value) return std::nullopt;
                return fingerprintNegate(*value);
            }
            if (head->name == reciprocalName) {
                auto value = evaluateFingerprint(
                    outer->argument, carrierName);
                if (!value) return std::nullopt;
                return fingerprintModularInverse(*value);
            }
        }
    }
    // Otherwise: opaque atom. Use the cached subtree hash mod p.
    return expression->hash % kFingerprintModulus;
}

// Build the "(fingerprint mod (2^64 - 59): …)" diagnostic suffix
// to append onto a ring/field failure. Always returns a string —
// even when the evaluator gives up, the user learns something.
std::string Elaborator::buildFingerprintDiagnostic(
    ExpressionPointer leftEndpoint,
    ExpressionPointer rightEndpoint,
    const std::string& carrierName) const {
    auto leftValue =
        evaluateFingerprint(leftEndpoint, carrierName);
    auto rightValue =
        evaluateFingerprint(rightEndpoint, carrierName);
    if (!leftValue || !rightValue) {
        return "\n(fingerprint mod (2^64 - 59): division by zero "
               "during evaluation — either a denominator that "
               "needs a nonzero hypothesis, or a 1-in-2^64 hash "
               "collision; can't diagnose either way)";
    }
    if (*leftValue == *rightValue) {
        return "\n(fingerprint mod (2^64 - 59): LHS = RHS = "
             + std::to_string(*leftValue)
             + " — the identity is almost certainly true; this "
               "looks like a tactic limitation, not a real "
               "mathematical mismatch)";
    }
    return "\n(fingerprint mod (2^64 - 59): LHS = "
         + std::to_string(*leftValue) + ", RHS = "
         + std::to_string(*rightValue)
         + " — the identity is FALSE as a polynomial / field "
           "identity; the goal as stated is not provable)";
}

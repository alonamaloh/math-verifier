#pragma once

// The arbitrary-precision integer behind the kernel's NaturalLiteral
// node (PLAN_FAST_NUMERALS). A thin seam over GMP's C++ class: every
// kernel/elaborator use goes through this alias and the helpers below,
// so a future backend swap touches one header.
//
// Trust note: NaturalValue arithmetic executed by the kernel's
// accelerated-op table is part of the trusted computing base (owner
// decision, 2026-07-10). The `make tests` self-check re-verifies the
// table against the library definitions on a sample range.

#include <gmpxx.h>

#include <cstdint>
#include <string>

using NaturalValue = mpz_class;

// Cheap, deterministic 64-bit digest for the subtree hash: the low
// limb mixed with the limb count. Collisions only cost a structural
// recursion (which compares the full values), never soundness.
inline uint64_t naturalValueHash(const NaturalValue& value) {
    uint64_t low = static_cast<uint64_t>(mpz_get_ui(value.get_mpz_t()));
    uint64_t size = static_cast<uint64_t>(mpz_size(value.get_mpz_t()));
    return low ^ (size << 56);
}

inline std::string naturalValueToString(const NaturalValue& value) {
    return value.get_str();
}

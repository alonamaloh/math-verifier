#pragma once

#include <cstdint>
#include <string>

// Subtree hashing primitives. Used by Level and Expression to cache a
// bottom-up structural hash on every node at construction time. The
// auto-prover then uses hash equality as a constant-time fast path
// before falling back to structural recursion.
//
// Hash is a non-cryptographic 64-bit FNV-1a mix. Cheap to compute,
// cheap to combine, low collision rate on the inputs we hash
// (kernel terms with bounded variant counts).

namespace subtree_hash {

constexpr uint64_t kSeed  = 0xcbf29ce484222325ULL;  // FNV-1a 64 offset
constexpr uint64_t kPrime = 0x100000001b3ULL;        // FNV-1a 64 prime

// Variant tags. Keep distinct and stable across builds; serialization
// is independent (it does not rely on the hash value).
constexpr uint64_t kTagBoundVariable   = 0x01;
constexpr uint64_t kTagFreeVariable    = 0x02;
constexpr uint64_t kTagSort            = 0x03;
constexpr uint64_t kTagPi              = 0x04;
constexpr uint64_t kTagLambda          = 0x05;
constexpr uint64_t kTagApplication     = 0x06;
constexpr uint64_t kTagConstant        = 0x07;
constexpr uint64_t kTagLet             = 0x08;
constexpr uint64_t kTagLevelConst      = 0x11;
constexpr uint64_t kTagLevelParam      = 0x12;
constexpr uint64_t kTagLevelSuccessor  = 0x13;
constexpr uint64_t kTagLevelMax        = 0x14;
constexpr uint64_t kTagLevelIMax       = 0x15;

inline uint64_t mix(uint64_t h, uint64_t x) {
    return (h ^ x) * kPrime;
}

inline uint64_t hashString(const std::string& s) {
    uint64_t h = kSeed;
    for (unsigned char c : s) {
        h = mix(h, c);
    }
    return h;
}

}  // namespace subtree_hash

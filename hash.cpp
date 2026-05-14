#include "hash.hpp"

uint64_t fnv1aHash(std::string_view bytes) {
    // FNV-1a 64-bit offset basis and prime.
    constexpr uint64_t offsetBasis = 0xcbf29ce484222325ULL;
    constexpr uint64_t prime = 0x100000001b3ULL;
    uint64_t hash = offsetBasis;
    for (unsigned char byte : bytes) {
        hash ^= byte;
        hash *= prime;
    }
    return hash;
}

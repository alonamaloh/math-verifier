#pragma once

#include <cstdint>
#include <string>
#include <string_view>

// FNV-1a 64-bit hash. Used only for cache validity — we just need to
// reliably notice when the source content of a `.math` file (or its
// transitive dependencies) has changed. Not cryptographic.
//
// FNV-1a is a well-known, simple, deterministic hash: produces the same
// 64-bit value on every machine for the same input bytes.
uint64_t fnv1aHash(std::string_view bytes);

// Convenience: hash a string by-reference.
inline uint64_t fnv1aHash(const std::string& text) {
    return fnv1aHash(std::string_view{text});
}

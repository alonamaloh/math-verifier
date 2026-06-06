#pragma once

#include "kernel/expression.hpp"
#include "kernel/kernel.hpp"
#include "kernel/level.hpp"

#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

// Binary serialization of kernel state for use in the per-file
// verification cache (.mathv files).
//
// The cache lets us avoid re-elaborating the whole library on every
// kernel run: a .mathv file stores the declarations a single .math
// added to the environment, plus enough metadata to detect when the
// cache is stale (source hash + direct-dependency hashes).
//
// Format (binary, little-endian, simple TLV-ish):
//   4 bytes  : magic "MTHV"
//   4 bytes  : format version (u32)
//   varies   : source path (length-prefixed string)
//   8 bytes  : source content hash (u64, FNV-1a)
//   varies   : module name (length-prefixed string)
//   4 bytes  : number of direct dependencies (u32)
//   per dep  : module name (length-prefixed string)
//              dep cache path (length-prefixed string)
//              dep source hash (u64)
//   4 bytes  : number of new declarations (u32)
//   per decl : tagged variant serialization (see writeDeclaration)
//   4 bytes  : number of new implicit-argument-count entries (u32)
//   per ent  : declaration name (length-prefixed) + count (u32)
//
// Strings are length-prefixed with a u32 byte count.
// Vectors are length-prefixed with a u32 element count.

struct SerializationError : std::runtime_error {
    using std::runtime_error::runtime_error;
};

// Information about a single dependency stored in the cache header.
struct CachedDependency {
    std::string moduleName;
    std::string cachePath;
    uint64_t sourceHash;
};

// Operator-registry entry added by this file: `operator (sym) on
// (leftType, rightType) := function`.
struct CachedOperatorRegistration {
    std::string operatorSymbol;
    std::string leftTypeName;
    std::string rightTypeName;
    std::string functionName;
};

// Overload-alias entry added by this file: `overload alias :=
// function`.
struct CachedOverloadRegistration {
    std::string aliasName;
    std::string functionName;
};

// Congruence-under-binder entry added by this file:
// `congruence_under_binder F := L`.
struct CachedCongruenceRegistration {
    std::string functionName;
    std::string lemmaName;
};

// Coercion-registry entry added by this file. May be a direct
// `coercion (S, T) := F` registration or a transitive entry computed
// from one. `chain` is the list of function names to compose; apply
// chain[0] first, then chain[1], etc.
struct CachedCoercionRegistration {
    std::string sourceTypeName;
    std::string targetTypeName;
    std::vector<std::string> chain;
};

// Canonical-instance-registry entry added by this file. The derived key
// fields (structure / carrier head names) and the carrier-parameter count
// are stored; the instance's type is re-fetched from the loaded
// declaration `termName` at replay time.
struct CachedInstanceRegistration {
    std::string structureName;
    std::string carrierName;
    std::string termName;
    int parameterCount;
};

// Canonical structure-BUNDLE registry entry added by this file:
// `(structure, carrier head) → bundle term`, e.g.
// `(Ring, Integer) → Integer.ring_bundle`. Lets `{r : Ring}` resolve from
// a concrete carrier (see Environment::canonicalBundleRegistry).
struct CachedBundleRegistration {
    std::string structureName;
    std::string carrierName;
    std::string termName;
};

// The full contents of a .mathv file, prior to (de)serialization.
struct CacheContents {
    std::string sourcePath;
    uint64_t sourceHash;
    std::string moduleName;
    std::vector<CachedDependency> dependencies;
    // Declarations added by this file, in insertion order.
    std::vector<std::pair<std::string, Declaration>> declarations;
    // Implicit-argument-count entries added by this file.
    std::vector<std::pair<std::string, int>> implicitArgumentCounts;
    // Operator-registry entries added by this file.
    std::vector<CachedOperatorRegistration> operatorRegistrations;
    // Overload-alias entries added by this file.
    std::vector<CachedOverloadRegistration> overloadRegistrations;
    // Congruence-under-binder entries added by this file.
    std::vector<CachedCongruenceRegistration> congruenceRegistrations;
    // Coercion-registry entries added by this file (direct and the
    // transitive-closure entries that the direct one introduced).
    std::vector<CachedCoercionRegistration> coercionRegistrations;
    // Canonical-instance-registry entries added by this file.
    std::vector<CachedInstanceRegistration> instanceRegistrations;
    // Canonical structure-bundle-registry entries added by this file.
    std::vector<CachedBundleRegistration> bundleRegistrations;
};

// Write `contents` to `path`. Throws SerializationError on I/O failure.
void writeCacheFile(const std::string& path, const CacheContents& contents);

// Read a cache from `path`. Throws SerializationError on I/O failure,
// missing file, magic/version mismatch, or malformed content.
CacheContents readCacheFile(const std::string& path);

#include "kernel/kernel.hpp"
#include "kernel/printer.hpp"

#include "timing.hpp"
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

bool kernelCheckInvariants = false;

// Instrumentation knobs. See kernel.hpp for the full contract. Defaults
// (zero / false) leave the kernel running unchanged; main.cpp populates
// them from KERNEL_STEP_LIMIT / KERNEL_TRACE / KERNEL_PROFILE env vars.
uint64_t kernelStepLimit = 0;
uint64_t kernelTraceInterval = 0;
bool kernelProfileEnabled = false;
std::size_t kernelDumpWidth = 240;
bool kernelCacheEnabled = false;
bool g_hashConsEnabled = false;

// invalidateKernelCaches() is defined later in this file, after the
// cache structures it touches; declared in kernel.hpp.

namespace hash_cons_detail {
struct ExpressionHasher {
    size_t operator()(const ExpressionPointer& p) const {
        return static_cast<size_t>(p->hash);
    }
};
struct ExpressionEqualer {
    bool operator()(const ExpressionPointer& a,
                    const ExpressionPointer& b) const {
        return structurallyEqual(a, b);
    }
};
// Global hash-cons table. Strong-ref so entries live forever once
// inserted — fine for one-shot verify runs (process exits at the
// end), but a long-running tool would want weak refs + periodic
// cleanup. Memory is bounded by the number of distinct subterms
// across the whole run.
std::unordered_set<ExpressionPointer,
                   ExpressionHasher,
                   ExpressionEqualer>
    table;
}  // namespace hash_cons_detail

ExpressionPointer internExpression(ExpressionPointer candidate) {
    if (!g_hashConsEnabled) return candidate;
    auto [iterator, inserted] =
        hash_cons_detail::table.insert(candidate);
    return *iterator;
}

namespace {

// Thread-local guard so that the postcondition checks (which themselves
// call back into inferType) don't recursively re-check their own work.
// We only run the invariant check at the outermost public-API call.
thread_local bool isCurrentlyCheckingInvariants = false;

// Per-top-level-call instrumentation state. Reset at the start of each
// public addAxiom/addDefinition/addInductive entry; used by the WHNF,
// isDefinitionallyEqual, and inferType bodies to detect runaway work,
// emit periodic tracing breadcrumbs, and tally δ-reductions.
//
// All accesses happen on the same thread that owns the kernel call, so a
// thread_local is sufficient — no atomics needed.
thread_local uint64_t kernelStepCounter = 0;

// Most recently observed expressions for each operation. We update these
// at every step (cheap shared_ptr copies) so that when the step limit
// fires, the resulting error can include a snippet of where the kernel
// was working. The "operation tag" identifies which call site we're in.
thread_local const char* kernelLastOperation = nullptr;
thread_local ExpressionPointer kernelLastLeft;
thread_local ExpressionPointer kernelLastRight;

// δ-reduction counts by definition name, populated only when
// kernelProfileEnabled is true. Emitted from the top-level entry-point
// wrapper when the call completes.
thread_local std::map<std::string, uint64_t> kernelProfileCounts;

// ---- WHNF memoization ----------------------------------------------------
//
// Keyed by **structural identity** (not pointer identity): the hash that
// every Expression carries is the bucket selector, and structurallyEqual
// is the bucket-equality test. This means two freshly-allocated but
// structurally-identical inputs hit the same cache entry — which is the
// whole point, since the elaborator hands the kernel many such pairs.
//
// Reset by KernelInstrumentationScope at each public-entry boundary, so
// the environment is constant for any single lookup and WHNF's answer
// depends only on the input expression.
//
// We intentionally do NOT cache isDefinitionallyEqual: its answer depends
// on the local Context (let-bindings, opened binders) which we'd have to
// fold into the key. WHNF, by contrast, only takes an Environment +
// expression — the cache is well-defined.
struct ExpressionStructuralHash {
    std::size_t operator()(const ExpressionPointer& expression) const noexcept {
        return expression ? static_cast<std::size_t>(expression->hash) : 0;
    }
};
struct ExpressionStructuralEqual {
    bool operator()(const ExpressionPointer& left,
                    const ExpressionPointer& right) const noexcept {
        if (left.get() == right.get()) return true;
        if (!left || !right) return false;
        return structurallyEqual(left, right);
    }
};
thread_local std::unordered_map<ExpressionPointer, ExpressionPointer,
                                ExpressionStructuralHash,
                                ExpressionStructuralEqual> whnfCache;

// Positive-result cache for isDefinitionallyEqual. Key: structural pair
// (left, right). We only cache TRUE results — a `false` may have been
// conservatively returned due to fuel exhaustion in a particular call,
// and reusing it elsewhere would be unsound. A true result, however, is
// a positive proof that the expressions are definitionally equal, and
// equality is symmetric and context-monotone (adding binders to context
// can only refine, not refute, equality of closed-under-FVs terms).
//
// Reset, like whnfCache, at every public-entry boundary because the
// environment is mutated there.
struct ExpressionPairStructuralHash {
    std::size_t operator()(
            const std::pair<ExpressionPointer, ExpressionPointer>& pair)
            const noexcept {
        uint64_t a = pair.first  ? pair.first->hash  : 0;
        uint64_t b = pair.second ? pair.second->hash : 0;
        // Combine the two hashes asymmetrically so (a,b) and (b,a) get
        // distinct bucket slots — the cache could be made symmetric, but
        // we want it to track the exact comparisons the caller performed.
        return static_cast<std::size_t>(a ^ (b * 0x9e3779b97f4a7c15ULL));
    }
};
struct ExpressionPairStructuralEqual {
    bool operator()(
            const std::pair<ExpressionPointer, ExpressionPointer>& left,
            const std::pair<ExpressionPointer, ExpressionPointer>& right)
            const noexcept {
        ExpressionStructuralEqual e;
        return e(left.first, right.first) && e(left.second, right.second);
    }
};
thread_local std::unordered_set<
    std::pair<ExpressionPointer, ExpressionPointer>,
    ExpressionPairStructuralHash,
    ExpressionPairStructuralEqual> isDefEqTrueCache;
thread_local uint64_t isDefEqCacheHits = 0;
thread_local uint64_t isDefEqCacheMisses = 0;

// ---- In-flight tracking (loop detection) ---------------------------------
//
// Track pointer-pairs currently being computed by isDefEq. If a recursive
// call re-enters a comparison that's already on the stack (without the
// cache having absorbed it — meaning the outer call hasn't returned yet),
// we're in a reduction loop: descending into subexpressions has brought us
// back to the same question. Bail out conservatively with `false`. The
// outer call's "no I'm not equal" answer is the right one for that level —
// either the expressions genuinely differ, or we'll know it because some
// caller fed us a non-terminating type.
//
// We track WHNF too: re-entering the same input mid-reduction is a
// definitional-equality loop (a definition that unfolds to mention
// itself). WHNF currently relies on fuel for that — loop detection is a
// cheaper, more informative termination signal.
thread_local std::unordered_set<ExpressionPointer,
                                ExpressionStructuralHash,
                                ExpressionStructuralEqual> whnfInFlight;
thread_local std::unordered_set<
    std::pair<ExpressionPointer, ExpressionPointer>,
    ExpressionPairStructuralHash,
    ExpressionPairStructuralEqual> isDefEqInFlight;
thread_local uint64_t isDefEqLoopsDetected = 0;
thread_local uint64_t whnfLoopsDetected = 0;
// Monotone counter bumped every time EITHER loop-detection short-circuit
// fires (WHNF returning its input unreduced, isDefEq returning a
// conservative `false`). A short-circuit's answer depends on what is
// in flight — i.e. on the CALL STACK — so any result computed while one
// fired beneath it is context-dependent and MUST NOT be memoised in the
// context-free caches: a fresh top-level call could reduce further (or
// decide equality) where the in-flight call could not. Cache writers
// snapshot this counter before computing and skip the insert when it
// moved. (Found via a redundancy-check poisoning bug: a speculative
// auto-prover search cut a reduction cycle, cached the partial WHNF, and
// a later — completely independent — defeq check at the theorem boundary
// read the poisoned entry and reported a kernel-true equality as false.)
thread_local uint64_t loopShortCircuitEpoch = 0;

// inferType cache — keyed by (expressionStructuralHash, contextFingerprint).
// inferType's result depends on Context (FreeVariable lookups), so the key
// includes a fingerprint of the context: XOR of per-entry hashes (entry
// name string-hash XOR entry type's structural hash). Two contexts with the
// same entry set produce the same fingerprint; different contexts produce
// different fingerprints with overwhelming probability. The cache lives for
// one declaration's checking pass, like the other kernel caches — cleared
// inside KernelInstrumentationScope.
//
// This is always-on (not gated on kernelCacheEnabled). Empirically, kernel
// caching is a clear win once allocator pressure is reduced (mimalloc),
// and inferType in particular shows up as the dominant `coerceToExpectedTypeViaDiff`
// cost in profiles even when each call is fresh — sub-expression recursion
// inside inferType hits the cache.
struct InferTypeCacheKey {
    uint64_t expressionHash;
    uint64_t contextFingerprint;
    bool operator==(const InferTypeCacheKey& other) const {
        return expressionHash == other.expressionHash
            && contextFingerprint == other.contextFingerprint;
    }
};
struct InferTypeCacheKeyHash {
    std::size_t operator()(const InferTypeCacheKey& k) const noexcept {
        return static_cast<std::size_t>(
            k.expressionHash ^ (k.contextFingerprint * 0x9e3779b97f4a7c15ULL));
    }
};
struct InferTypeCacheValue {
    ExpressionPointer expression;
    ExpressionPointer type;
};
// Multimap-style: hash collisions are rare but possible; we store the
// (expression, type) pair and check structuralEqual on lookup.
thread_local std::unordered_multimap<
    InferTypeCacheKey, InferTypeCacheValue,
    InferTypeCacheKeyHash> inferTypeCache;
thread_local uint64_t inferTypeCacheHits = 0;
thread_local uint64_t inferTypeCacheMisses = 0;

// The Environment all current cache entries were computed against. Every
// cached kernel result (WHNF, defeq-true, inferType) depends on the
// environment's declarations — but the caches are keyed by expression
// alone. The elaborator routinely queries a SECOND environment (the
// whole-library lemma-search snapshot used to enrich failing-proof errors
// with unimported-lemma suggestions, loaded WITHOUT definition bodies), and
// entries computed against one environment are wrong for the other: e.g.
// `Rational.to_real` δ-unfolds in the module environment but is stuck in
// the bodyless snapshot. Serving the wrong entry made a kernel-TRUE
// equality come back false at a theorem boundary (found via the
// redundancy checker, whose speculative failures trigger lemma searches).
// Guard: every cache consult first checks the requesting environment; a
// different owner wipes all caches and claims ownership.
thread_local const void* kernelCacheOwner = nullptr;

// Reduction-recursion depth bound. Fuel bounds the NUMBER of reduction
// steps, not the nesting of recursive WHNF/isDefEq frames — a runaway
// unfold whose every frame sees a NEW expression sails past loop
// detection and overflows the stack (observed as SIGSEGV with kernel
// caches disabled, where memoisation no longer keeps recursion shallow).
// The guard turns that into a clean TypeError well before the platform
// stack limit. At -O3 a WHNF level costs several KB of stack (wrapper +
// uncached body + helpers get merged into jumbo frames), so 500 nested
// levels is the safe ceiling; real proofs stay in the low hundreds even
// with caches off.
constexpr int kernelMaxReductionDepth = 500;
thread_local int kernelReductionDepth = 0;
struct ReductionDepthGuard {
    ReductionDepthGuard() {
        if (++kernelReductionDepth > kernelMaxReductionDepth) {
            --kernelReductionDepth;
            throw KernelResourceExhausted(
                "kernel reduction recursion exceeded the depth bound ("
                + std::to_string(kernelMaxReductionDepth)
                + "); the term needs deeper nested reduction than the "
                  "stack safely allows — most often a runaway unfold");
        }
    }
    ~ReductionDepthGuard() { --kernelReductionDepth; }
};
thread_local std::size_t kernelCacheOwnerSize = 0;

void ensureKernelCacheOwner(const Environment& environment) {
    // Owner address + declaration count: the count catches the (rare)
    // address-reuse case where a destroyed environment's storage is
    // recycled for a new one between public-entry boundaries.
    if (kernelCacheOwner == &environment
        && kernelCacheOwnerSize == environment.declarations.size()) {
        return;
    }
    whnfCache.clear();
    isDefEqTrueCache.clear();
    whnfInFlight.clear();
    isDefEqInFlight.clear();
    inferTypeCache.clear();
    kernelCacheOwner = &environment;
    kernelCacheOwnerSize = environment.declarations.size();
}

// Compute a fingerprint of `context` for inferType caching. XOR-fold per-
// entry hashes; commutative, but that's fine — Lean's `expr_map` does the
// same thing for its `m_infer_type` cache and the false-positive rate is
// negligible in practice. The empty context fingerprints to 0.
inline uint64_t contextFingerprint(const Context& context) {
    uint64_t fingerprint = 0;
    uint64_t mixer = 0x9e3779b97f4a7c15ULL;
    for (const auto& entry : context) {
        uint64_t nameHash = subtree_hash::hashString(entry.name);
        uint64_t typeHash = entry.type ? entry.type->hash : 0;
        // Mix name + type + origin (User vs Internal — the FV identity
        // includes both).
        uint64_t entryHash = nameHash ^ (typeHash * mixer)
            ^ static_cast<uint64_t>(entry.origin);
        fingerprint ^= entryHash;
        mixer *= 0x100000001b3ULL;  // walk through different mixers
    }
    return fingerprint;
}

// Implementation note: this function is declared in `kernel.hpp` (no
// namespace), so we close the anonymous namespace, define it, and
// reopen the namespace.
} // namespace
void invalidateKernelCaches() {
    if (kernelCacheEnabled) {
        whnfCache.clear();
        isDefEqTrueCache.clear();
        whnfInFlight.clear();
        isDefEqInFlight.clear();
    }
    // inferTypeCache is always-on; clear it whenever the kernel signals
    // a public-entry boundary (declaration commits, environment mutates).
    inferTypeCache.clear();
    kernelCacheOwner = nullptr;
}
// Public read-only accessor for the per-thread reduction-step counter.
// Defined here (after the anonymous namespace that declares it) so the
// auto-prover can express its effort budget in kernel reduction steps.
uint64_t kernelStepsSoFar() { return kernelStepCounter; }
namespace {

// Diagnostic counters for the cache, reported under KERNEL_PROFILE.
thread_local uint64_t whnfCacheHits = 0;
thread_local uint64_t whnfCacheMisses = 0;
thread_local uint64_t isDefEqCallCount = 0;
thread_local uint64_t whnfCallCount = 0;

// Render an expression for a diagnostic message. The full pretty-print
// can be huge; we truncate to keep error messages and trace breadcrumbs
// readable.
std::string renderForDiagnostic(ExpressionPointer expression) {
    if (!expression) return "<null>";
    std::string text = prettyPrint(expression);
    if (text.size() > kernelDumpWidth) {
        text = text.substr(0, kernelDumpWidth) + " …(+" +
               std::to_string(text.size() - kernelDumpWidth) + " bytes)";
    }
    return text;
}

// Bump the step counter and, if instrumentation is enabled, emit a
// breadcrumb every kernelTraceInterval steps and throw when the limit
// is reached. `operation` identifies the call site (a literal C string
// like "whnf" or "isDefEq"); `left` and `right` are the expressions
// currently being worked on (right may be null for unary operations).
//
// Inlined hot path: when both knobs are off (the default), this is one
// integer increment and two compares.
inline void kernelStep(const char* operation,
                       ExpressionPointer left,
                       ExpressionPointer right = nullptr) {
    ++kernelStepCounter;
    kernelLastOperation = operation;
    kernelLastLeft = left;
    kernelLastRight = right;
    if (kernelTraceInterval > 0 &&
        kernelStepCounter % kernelTraceInterval == 0) {
        std::fprintf(stderr,
                     "[kernel step %llu] %s\n"
                     "  left:  %s\n",
                     (unsigned long long)kernelStepCounter,
                     operation,
                     renderForDiagnostic(left).c_str());
        if (right) {
            std::fprintf(stderr,
                         "  right: %s\n",
                         renderForDiagnostic(right).c_str());
        }
    }
    if (kernelStepLimit > 0 && kernelStepCounter > kernelStepLimit) {
        // Dump the in-flight δ-profile before throwing — the destructor on
        // KernelInstrumentationScope WOULD do it on stack unwind, but in
        // practice the elaborator's outer error handling can swallow the
        // stderr ordering, so we emit it eagerly here as well.
        if (kernelProfileEnabled) {
            uint64_t whnfLookups = whnfCacheHits + whnfCacheMisses;
            uint64_t isDefEqLookups = isDefEqCacheHits + isDefEqCacheMisses;
            std::fprintf(
                stderr,
                "[kernel profile, on step-limit] %llu step(s), "
                "isDefEq %llu (cache %llu/%llu, %.1f%%, loops %llu), "
                "WHNF %llu (cache %llu/%llu, %.1f%%, loops %llu)\n",
                (unsigned long long)kernelStepCounter,
                (unsigned long long)isDefEqCallCount,
                (unsigned long long)isDefEqCacheHits,
                (unsigned long long)isDefEqCacheMisses,
                isDefEqLookups > 0
                    ? 100.0 * isDefEqCacheHits / isDefEqLookups : 0.0,
                (unsigned long long)isDefEqLoopsDetected,
                (unsigned long long)whnfCallCount,
                (unsigned long long)whnfCacheHits,
                (unsigned long long)whnfCacheMisses,
                whnfLookups > 0
                    ? 100.0 * whnfCacheHits / whnfLookups : 0.0,
                (unsigned long long)whnfLoopsDetected);
            std::vector<std::pair<uint64_t, std::string>> sorted;
            for (const auto& [name, count] : kernelProfileCounts) {
                sorted.emplace_back(count, name);
            }
            std::sort(sorted.begin(), sorted.end(),
                      [](const auto& a, const auto& b) {
                          return a.first > b.first;
                      });
            std::size_t shown = 0;
            for (const auto& [count, name] : sorted) {
                if (count < 100) break;
                if (shown++ >= 15) break;
                std::fprintf(stderr,
                             "  δ %-50s %llu\n",
                             name.c_str(),
                             (unsigned long long)count);
            }
        }
        std::string message =
            "kernel step limit (" + std::to_string(kernelStepLimit) +
            ") exceeded in " + std::string(operation) +
            "; aborting to prevent unbounded work.\n"
            "  left:  " + renderForDiagnostic(left);
        if (right) {
            message += "\n  right: " + renderForDiagnostic(right);
        }
        throw TypeError(std::move(message));
    }
}

// Count one δ-reduction of the named constant for profile reporting.
// No-op when profiling is off.
inline void kernelCountDelta(const std::string& constantName) {
    if (kernelProfileEnabled) {
        ++kernelProfileCounts[constantName];
    }
}

// Reset all per-top-level instrumentation state. Called from addAxiom /
// addDefinition / addInductive before any kernel work runs, and (if
// profiling is enabled) emits a one-line summary on completion via the
// KernelInstrumentationScope RAII guard below.
struct KernelInstrumentationScope {
    std::string declarationName;
    explicit KernelInstrumentationScope(std::string name)
            : declarationName(std::move(name)) {
        kernelStepCounter = 0;
        kernelLastOperation = nullptr;
        kernelLastLeft.reset();
        kernelLastRight.reset();
        kernelProfileCounts.clear();
        whnfCacheHits = 0;
        whnfCacheMisses = 0;
        isDefEqCacheHits = 0;
        isDefEqCacheMisses = 0;
        isDefEqCallCount = 0;
        whnfCallCount = 0;
        // The environment is about to be mutated (a new axiom / definition
        // / inductive added). Cached WHNF and isDefEq results computed
        // against the pre-mutation environment may no longer be correct
        // (e.g. a name that was previously stuck as a bare Constant now
        // δ-reduces), so wipe both caches before doing any more reduction
        // work.
        if (kernelCacheEnabled) {
            whnfCache.clear();
            isDefEqTrueCache.clear();
        }
        // The in-flight sets are call-stack bookkeeping (loop detection
        // runs regardless of caching); no kernel recursion is active at a
        // public-entry boundary, so clear them unconditionally.
        whnfInFlight.clear();
        isDefEqInFlight.clear();
        // inferTypeCache is always-on; clear at every public-entry
        // boundary along with the gated caches.
        inferTypeCache.clear();
        inferTypeCacheHits = 0;
        inferTypeCacheMisses = 0;
        isDefEqLoopsDetected = 0;
        whnfLoopsDetected = 0;
    }
    ~KernelInstrumentationScope() {
        if (kernelProfileEnabled) {
            uint64_t whnfLookups = whnfCacheHits + whnfCacheMisses;
            uint64_t isDefEqLookups = isDefEqCacheHits + isDefEqCacheMisses;
            std::fprintf(
                stderr,
                "[kernel profile] %s: %llu step(s), "
                "isDefEq %llu (cache %llu/%llu, %.1f%%, loops %llu), "
                "WHNF %llu (cache %llu/%llu, %.1f%%, loops %llu)\n",
                declarationName.c_str(),
                (unsigned long long)kernelStepCounter,
                (unsigned long long)isDefEqCallCount,
                (unsigned long long)isDefEqCacheHits,
                (unsigned long long)isDefEqCacheMisses,
                isDefEqLookups > 0
                    ? 100.0 * isDefEqCacheHits / isDefEqLookups : 0.0,
                (unsigned long long)isDefEqLoopsDetected,
                (unsigned long long)whnfCallCount,
                (unsigned long long)whnfCacheHits,
                (unsigned long long)whnfCacheMisses,
                whnfLookups > 0
                    ? 100.0 * whnfCacheHits / whnfLookups : 0.0,
                (unsigned long long)whnfLoopsDetected);
            // Sort by count desc, show top 10.
            std::vector<std::pair<uint64_t, std::string>> sorted;
            for (const auto& [name, count] : kernelProfileCounts) {
                sorted.emplace_back(count, name);
            }
            std::sort(sorted.begin(), sorted.end(),
                      [](const auto& a, const auto& b) {
                          return a.first > b.first;
                      });
            std::size_t shown = 0;
            for (const auto& [count, name] : sorted) {
                if (count < 100) break;
                if (shown++ >= 10) break;
                std::fprintf(stderr,
                             "  δ %-50s %llu\n",
                             name.c_str(),
                             (unsigned long long)count);
            }
        }
    }
};

// Rejects names that are empty, contain control characters, or begin with
// `@` (reserved by the printer for kernel-internal free variables). Used
// to validate every name a client passes through the public API. Cheap
// enough to leave always on.
void validateName(const std::string& name, const std::string& description) {
    if (name.empty()) {
        throw TypeError(description + ": empty name");
    }
    if (name[0] == '@') {
        throw TypeError(description + ": name '" + name +
                        "' must not begin with '@' (reserved)");
    }
    for (unsigned char c : name) {
        if (c < 0x20) {
            throw TypeError(description + ": name contains a control "
                            "character (byte value " +
                            std::to_string((int)c) + ")");
        }
    }
}

} // namespace

namespace {

// Kernel-private builder for Internal-origin free variables. Lives here
// (not in expression.hpp) so clients of the kernel cannot construct them
// through the public API.
ExpressionPointer makeInternalFreeVariable(std::string name) {
    uint64_t nameHash = subtree_hash::hashString(name);
    auto expression = makeRawExpression(
        FreeVariable{std::move(name), FreeVariableOrigin::Internal});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagFreeVariable),
            nameHash),
        static_cast<uint64_t>(FreeVariableOrigin::Internal));
    return expression;
}

// Lean's imax rule on level expressions: makeLevelIMax already encodes the
// Proposition-collapsing behaviour for concrete codomains and falls back to a
// symbolic LevelIMax otherwise.
LevelPointer impredicativeMaxLevel(LevelPointer domainLevel,
                                   LevelPointer codomainLevel) {
    return makeLevelIMax(std::move(domainLevel), std::move(codomainLevel));
}

}  // namespace

// Walks `expression`, replacing each universe parameter that appears in any
// Sort or in a Constant's universe arguments with the supplied substitution.
// Used by inferType when a polymorphic constant is referenced with explicit
// level arguments — every internal Sort and Constant in the declared type
// needs its level parameters instantiated.
ExpressionPointer substituteUniverseLevels(
    ExpressionPointer expression,
    const std::vector<std::string>& parameterNames,
    const std::vector<LevelPointer>& replacements) {
    if (parameterNames.size() != replacements.size()) {
        throw TypeError(
            "internal: substituteUniverseLevels called with mismatched "
            "parameter/replacement counts (" +
            std::to_string(parameterNames.size()) + " vs " +
            std::to_string(replacements.size()) + ")");
    }
    auto substituteOneLevel = [&](LevelPointer level) {
        for (std::size_t i = 0; i < parameterNames.size(); ++i) {
            level = substituteLevelParameter(level, parameterNames[i],
                                             replacements[i]);
        }
        return level;
    };

    if (auto* sort = std::get_if<Sort>(&expression->node)) {
        return makeSort(substituteOneLevel(sort->level));
    }
    if (auto* constant = std::get_if<Constant>(&expression->node)) {
        std::vector<LevelPointer> newArguments;
        newArguments.reserve(constant->universeArguments.size());
        for (auto& argument : constant->universeArguments) {
            newArguments.push_back(substituteOneLevel(argument));
        }
        return makeConstant(constant->name, std::move(newArguments));
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
                      substituteUniverseLevels(pi->domain,   parameterNames, replacements),
                      substituteUniverseLevels(pi->codomain, parameterNames, replacements));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
                          substituteUniverseLevels(lambda->domain, parameterNames, replacements),
                          substituteUniverseLevels(lambda->body,   parameterNames, replacements));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return makeApplication(
            substituteUniverseLevels(application->function, parameterNames, replacements),
            substituteUniverseLevels(application->argument, parameterNames, replacements));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return makeLet(let->displayHint,
                       substituteUniverseLevels(let->type,  parameterNames, replacements),
                       substituteUniverseLevels(let->value, parameterNames, replacements),
                       substituteUniverseLevels(let->body,  parameterNames, replacements));
    }
    // BoundVariable, FreeVariable: no levels inside, return as-is.
    return expression;
}

namespace {

// Helper accessor: every Declaration variant carries a list of universe
// parameter names. Returns it.
const std::vector<std::string>& declarationUniverseParameters(
    const Declaration& declaration) {
    if (auto* axiom       = std::get_if<Axiom>(&declaration))       return axiom->universeParameters;
    if (auto* definition  = std::get_if<Definition>(&declaration))  return definition->universeParameters;
    if (auto* inductive   = std::get_if<Inductive>(&declaration))   return inductive->universeParameters;
    if (auto* constructor = std::get_if<Constructor>(&declaration)) return constructor->universeParameters;
    if (auto* recursor    = std::get_if<Recursor>(&declaration))    return recursor->universeParameters;
    static const std::vector<std::string> empty;
    return empty;
}

// Returns the declared type of any Declaration. (For Inductive this is the
// `kind` field; for everything else it's `type`.)
ExpressionPointer declarationType(const Declaration& declaration) {
    if (auto* axiom       = std::get_if<Axiom>(&declaration))       return axiom->type;
    if (auto* definition  = std::get_if<Definition>(&declaration))  return definition->type;
    if (auto* inductive   = std::get_if<Inductive>(&declaration))   return inductive->kind;
    if (auto* constructor = std::get_if<Constructor>(&declaration)) return constructor->type;
    if (auto* recursor    = std::get_if<Recursor>(&declaration))    return recursor->type;
    throw TypeError("internal: unhandled Declaration variant");
}

} // namespace

ExpressionPointer shift(ExpressionPointer expression, int amount, int cutoff) {
    // Short-circuit: if the subtree's highest free BV is below cutoff,
    // shift is a no-op. Most subtrees are closed library terms, so
    // this skips the entire recursion in the common case.
    if (expression->maxFreeBoundVariable < cutoff) return expression;
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        if (boundVariable->deBruijnIndex >= cutoff) {
            return makeBoundVariable(boundVariable->deBruijnIndex + amount);
        }
        return expression;
    }
    if (std::holds_alternative<FreeVariable>(expression->node))   return expression;
    if (std::holds_alternative<Sort>(expression->node))           return expression;
    if (std::holds_alternative<Constant>(expression->node))       return expression;
    if (std::holds_alternative<NaturalLiteral>(expression->node)) return expression;
    // Structural-sharing fast path: if recursive shifts return the
    // same children (no BV at or above cutoff appeared in the subtree),
    // hand the original expression back unchanged. Most shifts touch
    // very few subterms; rebuilding the entire tree per shift was the
    // dominant cost in profiling.
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        auto newDomain   = shift(pi->domain,   amount, cutoff);
        auto newCodomain = shift(pi->codomain, amount, cutoff + 1);
        if (newDomain == pi->domain && newCodomain == pi->codomain) {
            return expression;
        }
        return makePi(pi->displayHint,
                      std::move(newDomain), std::move(newCodomain));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        auto newDomain = shift(lambda->domain, amount, cutoff);
        auto newBody   = shift(lambda->body,   amount, cutoff + 1);
        if (newDomain == lambda->domain && newBody == lambda->body) {
            return expression;
        }
        return makeLambda(lambda->displayHint,
                          std::move(newDomain), std::move(newBody));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        auto newFn  = shift(application->function, amount, cutoff);
        auto newArg = shift(application->argument, amount, cutoff);
        if (newFn == application->function
            && newArg == application->argument) {
            return expression;
        }
        return makeApplication(std::move(newFn), std::move(newArg));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        auto newType  = shift(let->type,  amount, cutoff);
        auto newValue = shift(let->value, amount, cutoff);
        auto newBody  = shift(let->body,  amount, cutoff + 1);
        if (newType == let->type && newValue == let->value
            && newBody == let->body) {
            return expression;
        }
        return makeLet(let->displayHint,
                       std::move(newType), std::move(newValue),
                       std::move(newBody));
    }
    throw TypeError("internal: unhandled Expression variant in shift");
}

ExpressionPointer substitute(ExpressionPointer expression,
                         int targetIndex,
                         ExpressionPointer replacement) {
    // Short-circuit: if the subtree has no free BV at or above
    // targetIndex, substitute is identity. Skips the entire recursion
    // on closed subtrees (the common case).
    if (expression->maxFreeBoundVariable < targetIndex) return expression;
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        if (boundVariable->deBruijnIndex == targetIndex) return replacement;
        if (boundVariable->deBruijnIndex >  targetIndex) {
            return makeBoundVariable(boundVariable->deBruijnIndex - 1);
        }
        return expression;
    }
    if (std::holds_alternative<FreeVariable>(expression->node))   return expression;
    if (std::holds_alternative<Sort>(expression->node))           return expression;
    if (std::holds_alternative<Constant>(expression->node))       return expression;
    if (std::holds_alternative<NaturalLiteral>(expression->node)) return expression;
    // Structural-sharing fast path: if recursive substitutes return the
    // same children, hand back the original. Most substitutes leave
    // most subterms untouched (the target BV appears in only one
    // branch). Rebuilding the entire tree per substitute was the
    // dominant cost in profiling.
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        auto newDomain   = substitute(pi->domain,   targetIndex,
                                       replacement);
        auto newCodomain = substitute(pi->codomain, targetIndex + 1,
                                       shift(replacement, 1));
        if (newDomain == pi->domain && newCodomain == pi->codomain) {
            return expression;
        }
        return makePi(pi->displayHint,
                      std::move(newDomain), std::move(newCodomain));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        auto newDomain = substitute(lambda->domain, targetIndex,
                                     replacement);
        auto newBody   = substitute(lambda->body,   targetIndex + 1,
                                     shift(replacement, 1));
        if (newDomain == lambda->domain && newBody == lambda->body) {
            return expression;
        }
        return makeLambda(lambda->displayHint,
                          std::move(newDomain), std::move(newBody));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        auto newFn  = substitute(application->function, targetIndex,
                                  replacement);
        auto newArg = substitute(application->argument, targetIndex,
                                  replacement);
        if (newFn == application->function
            && newArg == application->argument) {
            return expression;
        }
        return makeApplication(std::move(newFn), std::move(newArg));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        auto newType  = substitute(let->type,  targetIndex,
                                    replacement);
        auto newValue = substitute(let->value, targetIndex,
                                    replacement);
        auto newBody  = substitute(let->body,  targetIndex + 1,
                                    shift(replacement, 1));
        if (newType == let->type && newValue == let->value
            && newBody == let->body) {
            return expression;
        }
        return makeLet(let->displayHint,
                       std::move(newType), std::move(newValue),
                       std::move(newBody));
    }
    throw TypeError("internal: unhandled Expression variant in substitute");
}

ExpressionPointer openBinder(ExpressionPointer expression,
                             const std::string& freshName,
                             FreeVariableOrigin origin) {
    uint64_t nameHash = subtree_hash::hashString(freshName);
    auto freeVar = makeRawExpression(
        FreeVariable{freshName, origin});
    freeVar->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagFreeVariable),
            nameHash),
        static_cast<uint64_t>(origin));
    return substitute(std::move(expression), 0, std::move(freeVar));
}

namespace {

// Recursive helper for closeBinder. Walks `expression` while tracking the
// current binder depth (how many enclosing binders we've descended past
// since the close started).
ExpressionPointer closeAtDepth(ExpressionPointer expression,
                           const std::string& name,
                           FreeVariableOrigin origin,
                           int depth) {
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        // Any bound index referring to something outside `expression`
        // (i.e. an enclosing binder) must shift up by one because we are
        // adding a new binder at the outside. Indices below `depth` refer
        // to binders inside `expression` and are unchanged.
        if (boundVariable->deBruijnIndex >= depth) {
            return makeBoundVariable(boundVariable->deBruijnIndex + 1);
        }
        return expression;
    }
    if (auto* freeVariable = std::get_if<FreeVariable>(&expression->node)) {
        if (freeVariable->name == name && freeVariable->origin == origin) {
            return makeBoundVariable(depth);
        }
        return expression;
    }
    if (std::holds_alternative<Sort>(expression->node))           return expression;
    if (std::holds_alternative<Constant>(expression->node))       return expression;
    if (std::holds_alternative<NaturalLiteral>(expression->node)) return expression;
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
                      closeAtDepth(pi->domain,   name, origin, depth),
                      closeAtDepth(pi->codomain, name, origin, depth + 1));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
                          closeAtDepth(lambda->domain, name, origin, depth),
                          closeAtDepth(lambda->body,   name, origin, depth + 1));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return makeApplication(
            closeAtDepth(application->function, name, origin, depth),
            closeAtDepth(application->argument, name, origin, depth));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return makeLet(let->displayHint,
                       closeAtDepth(let->type,  name, origin, depth),
                       closeAtDepth(let->value, name, origin, depth),
                       closeAtDepth(let->body,  name, origin, depth + 1));
    }
    throw TypeError("internal: unhandled Expression variant in closeBinder");
}

} // namespace

ExpressionPointer closeBinder(ExpressionPointer expression,
                              const std::string& name,
                              FreeVariableOrigin origin) {
    return closeAtDepth(std::move(expression), name, origin, 0);
}

namespace {

// Peels an Application spine. Given `f a_1 a_2 ... a_n`, returns
// (f, [a_1, ..., a_n]) where the args are in application order.
struct AppSpine {
    ExpressionPointer head;
    std::vector<ExpressionPointer> args;
};
AppSpine peelApplicationSpine(ExpressionPointer expression) {
    AppSpine spine;
    spine.head = std::move(expression);
    while (auto* application = std::get_if<Application>(&spine.head->node)) {
        spine.args.push_back(application->argument);
        spine.head = application->function;
    }
    std::reverse(spine.args.begin(), spine.args.end());
    return spine;
}

// Re-applies a head to a sequence of arguments. The inverse of peelApplicationSpine.
ExpressionPointer applyArguments(ExpressionPointer head,
                                 const std::vector<ExpressionPointer>& args,
                                 std::size_t fromIndex = 0) {
    for (std::size_t i = fromIndex; i < args.size(); ++i) {
        head = makeApplication(head, args[i]);
    }
    return head;
}

// Builds the ι-reduction result. The recursor application is
//   recursor.{us} params... motive cases... indices... target
// where target reduces to a constructor application
//   constructor.{us'} params'... nonParamArgs...
// The result is the case for that constructor, applied to the non-param
// args (plus an inductive-hypothesis recursive call for each recursive
// non-param arg).
ExpressionPointer buildIotaReduction(
    const std::string& recursorName,
    const std::vector<LevelPointer>& recursorUniverseArguments,
    const Recursor& recursor,
    const Constructor& constructor,
    const std::vector<ExpressionPointer>& recursorArgs,
    const std::vector<ExpressionPointer>& constructorArgs) {
    int numParameters   = recursor.numParameters;
    int numConstructors = recursor.numConstructors;

    // The case for this constructor.
    auto result =
        recursorArgs[numParameters + 1 + constructor.constructorIndex];

    // Walk the constructor's declared type. The first numParameters Pis
    // are the parameter binders; skip them, substituting the matching
    // recursor parameter value into the codomain at each step.
    auto walker = constructor.type;
    int argIndex = 0;
    for (int p = 0; p < numParameters; ++p) {
        auto* pi = std::get_if<Pi>(&walker->node);
        if (!pi) {
            throw TypeError(
                "ι-reduction: constructor of inductive " +
                constructor.inductiveName +
                " has fewer Pi binders than the inductive has parameters");
        }
        walker = substitute(pi->codomain, 0, constructorArgs[argIndex]);
        argIndex++;
    }

    // Remaining Pis are non-param arguments. Apply the case to each one,
    // collecting an inductive-hypothesis recursive call for each recursive
    // argument; the hypotheses are applied AFTER all the values (the minor
    // premise binds every argument first, then the hypotheses in argument
    // order — Lean's layout, mirrored by buildCaseType).
    std::vector<ExpressionPointer> recursiveCalls;
    while (auto* pi = std::get_if<Pi>(&walker->node)) {
        auto argValue = constructorArgs[argIndex];
        result = makeApplication(result, argValue);

        // Detect recursive argument by peeling the type's Application chain.
        bool isRecursive = false;
        std::vector<ExpressionPointer> recursiveIndices;
        auto typeHead = pi->domain;
        std::vector<ExpressionPointer> typeArgs;
        while (auto* app = std::get_if<Application>(&typeHead->node)) {
            typeArgs.push_back(app->argument);
            typeHead = app->function;
        }
        std::reverse(typeArgs.begin(), typeArgs.end());
        if (auto* c = std::get_if<Constant>(&typeHead->node);
            c && c->name == recursor.inductiveName) {
            isRecursive = true;
            // Indices for the recursive call: the typeArgs past the params.
            for (std::size_t i = numParameters; i < typeArgs.size(); ++i) {
                recursiveIndices.push_back(typeArgs[i]);
            }
        }

        if (isRecursive) {
            // Build recursor.{us} params motive cases recursiveIndices argValue.
            auto recursiveCall =
                makeConstant(recursorName, recursorUniverseArguments);
            // Params + motive + cases (indices 0..numParameters + numConstructors).
            for (int i = 0; i <= numParameters + numConstructors; ++i) {
                recursiveCall = makeApplication(recursiveCall, recursorArgs[i]);
            }
            for (const auto& idx : recursiveIndices) {
                recursiveCall = makeApplication(recursiveCall, idx);
            }
            recursiveCall = makeApplication(recursiveCall, argValue);
            recursiveCalls.push_back(std::move(recursiveCall));
        }

        // Advance through the binder; substitute the arg value to keep
        // de Bruijn indices coherent in the remaining codomain.
        walker = substitute(pi->codomain, 0, argValue);
        argIndex++;
    }
    for (const auto& recursiveCall : recursiveCalls) {
        result = makeApplication(result, recursiveCall);
    }
    return result;
}

} // namespace

// ----------------------------------------------------------------------
// PLAN_FAST_NUMERALS §B — the NaturalLiteral/constructor bridge and the
// accelerated ground-arithmetic table.

// The one-peel constructor view of a literal: 0 ⇝ `zero`, n>0 ⇝
// `successor(NaturalLiteral(n-1))`. Recursors and defeq consume a
// literal one constructor at a time, on demand, so induction and
// pattern matching work over literals without ever materialising the
// full successor chain.
ExpressionPointer naturalLiteralConstructorView(const NaturalValue& value) {
    if (value == 0) return makeConstant("zero");
    return makeApplication(makeConstant("successor"),
                           makeNaturalLiteral(value - 1));
}

// Toggle for the accelerated-op table. The numeral-table self-check
// (driver.cpp, MATH_CHECK_NUMERAL_TABLE) turns it off so the library
// definitions themselves compute the reference results.
bool g_acceleratedNaturalOpsEnabled = true;

// Arity of an accelerated op, or 0 when `name` is not in the table.
// The table is part of the trusted computing base (owner decision,
// 2026-07-10): WHNF computes these ops on literals directly with GMP
// instead of unfolding the library recursion (which opacity blocks for
// most of them anyway). Each entry's semantics mirror the library
// definition EXACTLY, and the MATH_CHECK_NUMERAL_TABLE self-check
// re-verifies every entry against the definition bodies over a sample
// range.
//
// PLAN_KERNEL_EXPORT Stage 1: the op set and its conventions match
// Lean's kernel language (the core set of "Type Checking in Lean 4"
// minus beq/ble, which our ground relations prove via certificate
// lemmas instead): add/mul/sub/pow/div/mod semantics under our names
// add/multiply/monus/power/floor_divide/modulo, with (dividend,
// divisor) argument order, `n / 0 = 0`, `n % 0 = n`, and the exponent
// accelerated only below 2^24. factorial/maximum/predecessor have no
// Lean counterpart and are NOT table ops — they replay by unfolding.
int acceleratedNaturalOpArity(const std::string& name) {
    if (name == "Natural.add" || name == "Natural.multiply"
        || name == "Natural.monus" || name == "Natural.power"
        || name == "Natural.floor_divide" || name == "Natural.modulo") {
        return 2;
    }
    return 0;
}

// Evaluate an accelerated op on ground arguments. Empty optional means
// "decline" (an operand out of practical range, e.g. an exponent past
// unsigned long); the application is then left stuck, never mis-reduced.
std::optional<NaturalValue> evaluateAcceleratedNaturalOp(
    const std::string& name, const std::vector<NaturalValue>& arguments) {
    if (name == "Natural.add") {
        return NaturalValue(arguments[0] + arguments[1]);
    }
    if (name == "Natural.multiply") {
        return NaturalValue(arguments[0] * arguments[1]);
    }
    if (name == "Natural.monus") {
        // monus(a, b) = a - b, truncated at zero.
        if (arguments[0] <= arguments[1]) return NaturalValue(0);
        return NaturalValue(arguments[0] - arguments[1]);
    }
    if (name == "Natural.power") {
        // power(base, exponent) = base^exponent; power(base, 0) = 1.
        // Accelerate only exponents below 2^24 — Lean's cap, so we never
        // certify by defeq what an external checker declines to replay.
        if (!arguments[1].fits_ulong_p()
            || arguments[1] >= (1ul << 24)) {
            return std::nullopt;
        }
        NaturalValue result;
        mpz_pow_ui(result.get_mpz_t(), arguments[0].get_mpz_t(),
                   arguments[1].get_ui());
        return result;
    }
    if (name == "Natural.floor_divide") {
        // floor_divide(dividend, divisor); n / 0 = 0 (Lean's convention,
        // matched by the definition's `cases` guard on the divisor).
        if (arguments[1] == 0) return NaturalValue(0);
        NaturalValue result;
        mpz_fdiv_q(result.get_mpz_t(), arguments[0].get_mpz_t(),
                   arguments[1].get_mpz_t());
        return result;
    }
    if (name == "Natural.modulo") {
        // modulo(dividend, divisor); n % 0 = n (Lean's convention — the
        // fuel recursion carries the dividend when the divisor is zero).
        if (arguments[1] == 0) return arguments[0];
        NaturalValue result;
        mpz_fdiv_r(result.get_mpz_t(), arguments[0].get_mpz_t(),
                   arguments[1].get_mpz_t());
        return result;
    }
    return std::nullopt;
}

namespace {

// True when `name` resolves to the given constructor of the inductive
// `Natural` in this environment — guards the literal hooks against a
// user type that happens to reuse the constructor names.
bool isNaturalConstructor(const Environment& environment,
                          const std::string& name) {
    auto* declaration = environment.lookup(name);
    auto* constructor =
        declaration ? std::get_if<Constructor>(declaration) : nullptr;
    return constructor && constructor->inductiveName == "Natural";
}

} // namespace

namespace {

// Body of WHNF without the caching wrapper. Made anonymous so callers
// always go through the cached entry point below.
ExpressionPointer weakHeadNormalFormUncached(const Environment& environment,
                                             ExpressionPointer expression,
                                             int fuel) {
    while (true) {
        kernelStep("whnf", expression);
        if (--fuel <= 0) {
            throw KernelResourceExhausted(
                "weakHeadNormalForm: reduction did not terminate within "
                "fuel limit; expression may be ill-typed");
        }
        // δ-reduction on a bare Constant referring to a Definition. If the
        // definition is universe-polymorphic, instantiate its body with the
        // supplied universe arguments before unfolding. Refuses to reduce
        // (and throws) if the Constant's universe arity disagrees with the
        // Definition's — this can only happen on malformed input, since
        // inferType would have caught it; the check is defensive.
        if (auto* constant = std::get_if<Constant>(&expression->node)) {
            if (auto* declaration = environment.lookup(constant->name)) {
                if (auto* definition = std::get_if<Definition>(declaration)) {
                    // Opaque definitions block δ-unfolding. The kernel
                    // treats the Constant as a stuck head (like an
                    // axiom for reduction purposes); equality requires
                    // matching head + structurally equal arguments.
                    // Proofs that need the body must invoke the
                    // surface `unfold` form or named lemmas.
                    if (definition->opacity == Opacity::Opaque) {
                        return expression;
                    }
                    if (definition->universeParameters.size()
                            != constant->universeArguments.size()) {
                        throw TypeError(
                            "weakHeadNormalForm: constant " + constant->name +
                            " referenced with " +
                            std::to_string(constant->universeArguments.size()) +
                            " universe argument(s); definition declares " +
                            std::to_string(definition->universeParameters.size()));
                    }
                    kernelCountDelta(constant->name);
                    auto body = definition->body;
                    if (!definition->universeParameters.empty()) {
                        body = substituteUniverseLevels(
                            body,
                            definition->universeParameters,
                            constant->universeArguments);
                    }
                    expression = body;
                    continue;
                }
            }
            return expression;
        }
        // ζ-reduction on a Let.
        if (auto* let = std::get_if<Let>(&expression->node)) {
            expression = substitute(let->body, 0, let->value);
            continue;
        }
        // Application: peel the spine, reduce the head, then try β or ι.
        if (std::holds_alternative<Application>(expression->node)) {
            auto spine = peelApplicationSpine(expression);
            // Accelerated-op table, dispatched on the RAW head name
            // BEFORE the head is reduced: a TRANSPARENT table op
            // (`Natural.multiply`) would otherwise δ-unfold into its
            // recursor body and grind out the product in unary — the
            // table would never see it (only opaque `Natural.add`
            // survived head reduction as a stuck constant). A table op
            // whose arguments are all GROUND naturals — a literal,
            // `zero`, or a successor chain over either, in any mixture
            // — computes directly via GMP (the trusted-op table).
            // Reading every ground spelling (not just literals) keeps
            // the table from splitting defeq classes: `add(1, zero)`
            // and `add(1, 0)` must reduce to the SAME literal, or two
            // previously-convertible terms would normalize apart.
            // Non-ground arguments fall through to normal reduction.
            if (auto* rawHeadConstant =
                    std::get_if<Constant>(&spine.head->node)) {
                if (int arity =
                        acceleratedNaturalOpArity(rawHeadConstant->name);
                    g_acceleratedNaturalOpsEnabled && arity > 0
                    && static_cast<int>(spine.args.size()) >= arity) {
                    auto groundNaturalValue =
                        [&](ExpressionPointer argument)
                            -> std::optional<NaturalValue> {
                        NaturalValue offset = 0;
                        for (int guard = 0; guard < 100000; ++guard) {
                            if (auto* literal = std::get_if<NaturalLiteral>(
                                    &argument->node)) {
                                return NaturalValue(offset + literal->value);
                            }
                            if (std::holds_alternative<BoundVariable>(
                                    argument->node)
                                || std::holds_alternative<FreeVariable>(
                                       argument->node)) {
                                return std::nullopt;
                            }
                            ExpressionPointer reduced = weakHeadNormalForm(
                                environment, argument, fuel);
                            if (auto* literal = std::get_if<NaturalLiteral>(
                                    &reduced->node)) {
                                return NaturalValue(offset + literal->value);
                            }
                            if (auto* constant = std::get_if<Constant>(
                                    &reduced->node)) {
                                if (constant->name == "zero"
                                    && isNaturalConstructor(
                                           environment, "zero")) {
                                    return offset;
                                }
                                return std::nullopt;
                            }
                            if (auto* application = std::get_if<Application>(
                                    &reduced->node)) {
                                auto* head = std::get_if<Constant>(
                                    &application->function->node);
                                if (head && head->name == "successor"
                                    && isNaturalConstructor(
                                           environment, "successor")) {
                                    ++offset;
                                    argument = application->argument;
                                    continue;
                                }
                            }
                            return std::nullopt;
                        }
                        return std::nullopt;
                    };
                    std::vector<NaturalValue> groundArguments;
                    bool allGround = true;
                    for (int i = 0; i < arity && allGround; ++i) {
                        if (auto value = groundNaturalValue(spine.args[i])) {
                            groundArguments.push_back(std::move(*value));
                        } else {
                            allGround = false;
                        }
                    }
                    if (allGround) {
                        if (auto result = evaluateAcceleratedNaturalOp(
                                rawHeadConstant->name, groundArguments)) {
                            expression = applyArguments(
                                makeNaturalLiteral(std::move(*result)),
                                spine.args, arity);
                            continue;
                        }
                    }
                }
            }
            spine.head = weakHeadNormalForm(environment, spine.head, fuel);

            // β-reduction: if the head is a Lambda and we have at least one arg.
            if (auto* lambda = std::get_if<Lambda>(&spine.head->node);
                lambda && !spine.args.empty()) {
                expression = substitute(lambda->body, 0, spine.args[0]);
                expression = applyArguments(expression, spine.args, 1);
                continue;
            }

            // ι-reduction: if the head is a Constant referring to a Recursor
            // and we have enough args, with the target being a constructor
            // application of the right inductive type.
            if (auto* headConstant = std::get_if<Constant>(&spine.head->node)) {
                // PLAN_FAST_NUMERALS §B — literal re-compaction and the
                // accelerated-op table.
                //
                // `successor(NaturalLiteral(n))` compacts eagerly to
                // `NaturalLiteral(n+1)`, so ground terms re-enter literal
                // form after a constructor peel. Deliberately LITERAL-only
                // (a legacy `successor(zero)` chain keeps its shape): the
                // compaction exists to undo the one-peel constructor view,
                // not to re-canonicalise constructor spellings the
                // elaborator's matchers may still expect.
                if (headConstant->name == "successor"
                    && !spine.args.empty()
                    && isNaturalConstructor(environment, "successor")) {
                    ExpressionPointer argument = spine.args[0];
                    if (!std::holds_alternative<NaturalLiteral>(
                            argument->node)
                        && (std::holds_alternative<Application>(
                                argument->node)
                            || std::holds_alternative<Constant>(
                                   argument->node)
                            || std::holds_alternative<Let>(
                                   argument->node))) {
                        auto reduced = weakHeadNormalForm(
                            environment, argument, fuel);
                        if (std::holds_alternative<NaturalLiteral>(
                                reduced->node)) {
                            argument = reduced;
                        }
                    }
                    if (auto* literal =
                            std::get_if<NaturalLiteral>(&argument->node)) {
                        expression = applyArguments(
                            makeNaturalLiteral(literal->value + 1),
                            spine.args, 1);
                        continue;
                    }
                }
                // (The accelerated-op table dispatched above, on the
                // raw head, before this point — see the pre-reduction
                // block. Heads that survive reduction as stuck
                // constants were already covered there.)
                auto* declaration = environment.lookup(headConstant->name);
                if (auto* recursor = (declaration ? std::get_if<Recursor>(declaration)
                                                  : nullptr)) {
                    int needed = recursor->numParameters + 1
                               + recursor->numConstructors
                               + recursor->numIndices + 1;
                    if ((int)spine.args.size() >= needed) {
                        // Reduce the target to whnf and inspect.
                        auto reducedTarget =
                            weakHeadNormalForm(environment, spine.args[needed - 1], fuel);
                        // A literal target of Natural's recursor exposes
                        // its constructor view one peel at a time
                        // (PLAN_FAST_NUMERALS §B), so ι fires on ground
                        // literals exactly as it does on `zero`/`successor`.
                        if (recursor->inductiveName == "Natural") {
                            if (auto* literalTarget = std::get_if<NaturalLiteral>(
                                    &reducedTarget->node)) {
                                reducedTarget = naturalLiteralConstructorView(
                                    literalTarget->value);
                            }
                        }
                        auto targetSpine = peelApplicationSpine(reducedTarget);
                        if (auto* ctorConstant =
                                std::get_if<Constant>(&targetSpine.head->node)) {
                            auto* targetDeclaration =
                                environment.lookup(ctorConstant->name);
                            if (auto* constructor =
                                    (targetDeclaration ? std::get_if<Constructor>(targetDeclaration)
                                                : nullptr);
                                constructor &&
                                constructor->inductiveName == recursor->inductiveName) {
                                // Defensive universe-argument compatibility
                                // check: the constructor's universe args
                                // must match the prefix of the recursor's.
                                // (Currently the two sets are the same size;
                                // when universe-polymorphic motives land,
                                // the recursor will have one extra trailing
                                // universe arg for the motive level.) On
                                // mismatch, refuse to ι-reduce; the
                                // expression is stuck.
                                const auto& recursorArgs =
                                    headConstant->universeArguments;
                                const auto& constructorArgs =
                                    ctorConstant->universeArguments;
                                bool prefixMatches =
                                    constructorArgs.size() <= recursorArgs.size();
                                for (std::size_t i = 0;
                                     prefixMatches && i < constructorArgs.size();
                                     ++i) {
                                    if (!levelsDefinitionallyEqual(
                                            recursorArgs[i],
                                            constructorArgs[i])) {
                                        prefixMatches = false;
                                    }
                                }
                                if (!prefixMatches) {
                                    return applyArguments(spine.head, spine.args);
                                }
                                // Also verify the parameter values match.
                                // The recursor's first numParameters value
                                // args are the inductive's parameters; the
                                // constructor's first numParameters value
                                // args must agree definitionally.
                                bool parameterValuesMatch = true;
                                int paramCount = recursor->numParameters;
                                if ((int)targetSpine.args.size() < paramCount) {
                                    parameterValuesMatch = false;
                                }
                                for (int i = 0;
                                     parameterValuesMatch && i < paramCount;
                                     ++i) {
                                    if (!isDefinitionallyEqual(
                                            environment, {},
                                            spine.args[i],
                                            targetSpine.args[i], fuel)) {
                                        parameterValuesMatch = false;
                                    }
                                }
                                if (!parameterValuesMatch) {
                                    return applyArguments(spine.head, spine.args);
                                }
                                // ι-reduce.
                                auto reduced = buildIotaReduction(
                                    headConstant->name,
                                    headConstant->universeArguments,
                                    *recursor, *constructor,
                                    spine.args, targetSpine.args);
                                // Re-apply any extra arguments past `needed`.
                                expression = applyArguments(reduced, spine.args, needed);
                                continue;
                            }
                        }
                    }
                }

                // Quotient lift reduction: Quotient.lift(T, R, U, f, h,
                // Quotient.class_of(T, R, x)) reduces to f(x). The axioms in
                // `library/Logic/quotient.math` give Quotient.lift and
                // Quotient.class_of specific arities (6 and 3 value args); we
                // recognise them by name. Without this rule, every
                // computation on a quotient value would need an
                // explicit `Quotient.compute` transport.
                if (headConstant->name == "Quotient.lift"
                    && spine.args.size() >= 6) {
                    auto reducedQ = weakHeadNormalForm(
                        environment, spine.args[5], fuel);
                    auto qSpine = peelApplicationSpine(reducedQ);
                    if (auto* mkHead = std::get_if<Constant>(
                            &qSpine.head->node);
                        mkHead && mkHead->name == "Quotient.class_of"
                        && qSpine.args.size() >= 3) {
                        ExpressionPointer x = qSpine.args[2];
                        ExpressionPointer f = spine.args[3];
                        ExpressionPointer reduced =
                            makeApplication(f, x);
                        expression = applyArguments(reduced,
                                                     spine.args, 6);
                        continue;
                    }
                }
            }

            // No reduction possible. Rebuild and return.
            return applyArguments(spine.head, spine.args);
        }
        return expression;
    }
}

} // namespace

ExpressionPointer weakHeadNormalForm(const Environment& environment,
                                     ExpressionPointer expression,
                                     int fuel) {
    // Structural-hash memoization. Embedders opt in by setting
    // kernelCacheEnabled at startup — when true, the cache lives across
    // all WHNF calls and is automatically wiped at each public addAxiom
    // / addDefinition / addInductive boundary (since those mutate the
    // environment that WHNF reads).
    //
    // The cache is keyed by structural hash + structurallyEqual so
    // distinct ExpressionPointers with identical structure share one
    // entry. That's where the real savings come from on deeply nested
    // goals: the elaborator hands us many freshly-allocated but
    // structurally-identical subexpressions, and we reduce each shape
    // only once.
    //
    // Default (kernelCacheEnabled = false) preserves the unmemoised
    // contract the test suite relies on (e.g. "WHNF throws on fuel
    // exhaustion" — a cached result would silently bypass the throw).
    ++whnfCallCount;
    ReductionDepthGuard depthGuard;
    if (kernelCacheEnabled) {
        ensureKernelCacheOwner(environment);
    }
    if (auto cached = kernelCacheEnabled
            ? whnfCache.find(expression) : whnfCache.end();
        cached != whnfCache.end()) {
        ++whnfCacheHits;
        // Diagnostic (MATH_WHNF_CACHE_VERIFY=1): recompute every hit
        // uncached and flag entries that no longer reproduce.
        if (std::getenv("MATH_WHNF_CACHE_VERIFY")) {
            ExpressionPointer fresh;
            bool threw = false;
            try {
                fresh = weakHeadNormalFormUncached(
                    environment, expression, fuel);
            } catch (...) {
                threw = true;
            }
            if (!threw && fresh && !structurallyEqual(fresh, cached->second)) {
                std::fprintf(stderr,
                    "[whnf-poison] cached entry differs from fresh\n"
                    "  input:  %s\n  cached: %s\n  fresh:  %s\n",
                    renderForDiagnostic(expression).c_str(),
                    renderForDiagnostic(cached->second).c_str(),
                    renderForDiagnostic(fresh).c_str());
                return fresh;
            }
        }
        return cached->second;
    }
    // Loop detection: a recursive WHNF call landing on the SAME input
    // (structurally) before the outer call completed means the reduction
    // chain has come back to itself — no possible further progress, so
    // return the input unchanged. Without this the kernel would unfold
    // δ-recursively until fuel ran out.
    // Loop detection runs regardless of result caching: without it a
    // reduction cycle recurses until the STACK overflows (the fuel
    // counter bounds steps, not frame depth — observed as a SIGSEGV
    // under MATH_KERNEL_CACHE=0). The in-flight set is pure call-stack
    // bookkeeping, so it is sound with caching disabled.
    if (whnfInFlight.find(expression) != whnfInFlight.end()) {
        ++whnfLoopsDetected;
        ++loopShortCircuitEpoch;
        return expression;
    }
    ++whnfCacheMisses;
    ExpressionPointer key = expression;
    whnfInFlight.insert(key);
    uint64_t epochBefore = loopShortCircuitEpoch;
    ExpressionPointer result;
    try {
        result = weakHeadNormalFormUncached(
            environment, std::move(expression), fuel);
    } catch (...) {
        whnfInFlight.erase(key);
        throw;
    }
    whnfInFlight.erase(key);
    // Only successful reductions reach here; if the uncached body threw
    // (fuel exhaustion, malformed input), the cache stays unpolluted.
    // A result computed while a loop-detection short-circuit fired below
    // us is stack-dependent (see loopShortCircuitEpoch) — don't memoise.
    if (kernelCacheEnabled && loopShortCircuitEpoch == epochBefore)
        whnfCache.emplace(std::move(key), result);
    return result;
}

namespace {

// Generates a name for an Internal-origin free variable, used by
// isDefinitionallyEqual to open a Pi or Lambda binder for
// recursion. Uniqueness within the call tree comes from the context size,
// which strictly increases with each opening. The name itself is plain
// text — collision with user-supplied names is impossible because user
// names live in the User origin and these in the Internal origin.
std::string makeOpeningName(const Context& context) {
    return "v" + std::to_string(context.size());
}

} // namespace

// Cheap, allocation-free structural equality (alpha-equivalent since
// we use de Bruijn indices). Returns true only on truly identical
// terms — does not perform any reductions. Used as a fast path at the
// top of isDefinitionallyEqual: if two terms are structurally equal
// they are definitionally equal, and we save the WHNF + recurse cost.
// Bounded by expression depth; pointer-identity short-circuit at every
// level prunes aggressively once we hit shared subtrees.
bool structurallyEqual(ExpressionPointer left, ExpressionPointer right) {
    if (left.get() == right.get()) return true;
    // Hash fast-reject: bottom-up structural hashes are populated at
    // construction. A mismatch is a definitive "not equal"; a match
    // means we still recurse, since hash collisions are possible.
    if (left->hash != right->hash) return false;
    if (left->node.index() != right->node.index()) return false;
    if (auto* leftBound = std::get_if<BoundVariable>(&left->node)) {
        auto* rightBound = std::get_if<BoundVariable>(&right->node);
        return leftBound->deBruijnIndex == rightBound->deBruijnIndex;
    }
    if (auto* leftFree = std::get_if<FreeVariable>(&left->node)) {
        auto* rightFree = std::get_if<FreeVariable>(&right->node);
        return leftFree->name == rightFree->name
            && leftFree->origin == rightFree->origin;
    }
    if (auto* leftSort = std::get_if<Sort>(&left->node)) {
        auto* rightSort = std::get_if<Sort>(&right->node);
        return levelsDefinitionallyEqual(leftSort->level, rightSort->level);
    }
    if (auto* leftPi = std::get_if<Pi>(&left->node)) {
        auto* rightPi = std::get_if<Pi>(&right->node);
        return structurallyEqual(leftPi->domain, rightPi->domain)
            && structurallyEqual(leftPi->codomain, rightPi->codomain);
    }
    if (auto* leftLambda = std::get_if<Lambda>(&left->node)) {
        auto* rightLambda = std::get_if<Lambda>(&right->node);
        return structurallyEqual(leftLambda->domain, rightLambda->domain)
            && structurallyEqual(leftLambda->body,    rightLambda->body);
    }
    if (auto* leftApplication = std::get_if<Application>(&left->node)) {
        auto* rightApplication = std::get_if<Application>(&right->node);
        return structurallyEqual(leftApplication->function,
                                  rightApplication->function)
            && structurallyEqual(leftApplication->argument,
                                  rightApplication->argument);
    }
    if (auto* leftConstant = std::get_if<Constant>(&left->node)) {
        auto* rightConstant = std::get_if<Constant>(&right->node);
        if (leftConstant->name != rightConstant->name) return false;
        if (leftConstant->universeArguments.size()
                != rightConstant->universeArguments.size()) {
            return false;
        }
        for (size_t i = 0; i < leftConstant->universeArguments.size(); ++i) {
            if (!levelsDefinitionallyEqual(
                    leftConstant->universeArguments[i],
                    rightConstant->universeArguments[i])) {
                return false;
            }
        }
        return true;
    }
    if (auto* leftLet = std::get_if<Let>(&left->node)) {
        auto* rightLet = std::get_if<Let>(&right->node);
        return structurallyEqual(leftLet->type,  rightLet->type)
            && structurallyEqual(leftLet->value, rightLet->value)
            && structurallyEqual(leftLet->body,  rightLet->body);
    }
    if (auto* leftLiteral = std::get_if<NaturalLiteral>(&left->node)) {
        auto* rightLiteral = std::get_if<NaturalLiteral>(&right->node);
        return leftLiteral->value == rightLiteral->value;
    }
    return false;
}

// δ-reduce FreeVariables whose context entry carries a value (i.e.
// let-style binders). Walks `expression`, replacing matching FVs with
// shifted values. Iterates to a fixed point so cascading let-bindings
// (a later let whose value mentions an earlier let-name) fully unfold.
// Returns `expression` unchanged when no let-bound FVs are in scope —
// the common case — so the cost is negligible for non-let proofs.
ExpressionPointer deltaReduceLetFreeVariables(ExpressionPointer expression,
                                              const Context& context) {
    // Build the name → value map once. Skip if empty (no let-binders).
    std::map<std::pair<std::string, FreeVariableOrigin>, ExpressionPointer>
        assignment;
    for (const auto& entry : context) {
        if (entry.value) {
            assignment[{entry.name, entry.origin}] = entry.value;
        }
    }
    if (assignment.empty()) return expression;
    // Recursive walk. depth tracks how many binders we've descended into,
    // used to shift the replacement when substituting.
    std::function<ExpressionPointer(ExpressionPointer, int)> walk;
    walk = [&](ExpressionPointer expr, int depth) -> ExpressionPointer {
        if (auto* fv = std::get_if<FreeVariable>(&expr->node)) {
            auto iter = assignment.find({fv->name, fv->origin});
            if (iter != assignment.end()) {
                return shift(iter->second, depth);
            }
            return expr;
        }
        if (std::holds_alternative<BoundVariable>(expr->node)) return expr;
        if (std::holds_alternative<Sort>(expr->node))          return expr;
        if (std::holds_alternative<Constant>(expr->node))      return expr;
        if (auto* pi = std::get_if<Pi>(&expr->node)) {
            return makePi(pi->displayHint,
                          walk(pi->domain, depth),
                          walk(pi->codomain, depth + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&expr->node)) {
            return makeLambda(lambda->displayHint,
                              walk(lambda->domain, depth),
                              walk(lambda->body, depth + 1));
        }
        if (auto* app = std::get_if<Application>(&expr->node)) {
            return makeApplication(walk(app->function, depth),
                                   walk(app->argument, depth));
        }
        if (auto* let = std::get_if<Let>(&expr->node)) {
            return makeLet(let->displayHint,
                           walk(let->type,  depth),
                           walk(let->value, depth),
                           walk(let->body,  depth + 1));
        }
        return expr;
    };
    return walk(expression, 0);
}

// `opaque` is HARD by default: an opaque constant is never force-unfolded by
// the kernel/elaborator demand-point bridges — the only way to see through one
// is an explicit `unfold X in …`. (During the predictability experiment this
// was gated per-name by the MATH_HARD_OPAQUE env var; that gate is now retired
// and hard is the standing behaviour for every opaque VALUE definition. This
// remains the single decision point should a future `reducible` marker want
// to opt a specific definition back into δ-reduction.)
//
// EXCEPTION (D Phase-1, 2026-07-02): an opaque QUOTIENT-TYPE ALIAS — a
// definition whose body is literally `Quotient(T, R)` (the same class
// `engageOpaqueQuotientAlias` recognizes: Integer, Rational, the sealed
// Real) — is SOFT. Its home file's constructions are elaborated with the
// alias engaged, so their stored bodies apply `Quotient.lift`-typed
// functions to alias-typed arguments; a consumer that unfolds such a
// transparent construction (a cases motive re-check, a normalized goal)
// then needs the leaf defeq `Alias ≡ Quotient(T, R)` or the term does not
// Owner decision (2026-07-02): opacity is HARD for ALL opaque
// definitions, quotient-type aliases included — the AliasBridgeScope
// softening was reverted. The D-part interface-module machinery seals
// at the CACHE boundary (abstract axioms), so consumers never face the
// alias-defeq question at all; a home-file construction that needs the
// alias fact states it through the boundary lemmas. Kept as a function
// (the single decision point) for a possible future `reducible` opt-in.
bool isHardOpaqueConstant(const Environment& /*environment*/,
                          const std::string& /*name*/) {
    return true;
}

// True if any entry in `context` is a let-style binder (carries a value).
// Used by the isDefEq cache to skip caching when ζ-reduction makes the
// answer context-dependent.
namespace {
bool contextHasLetBinders(const Context& context) {
    for (const auto& entry : context) {
        if (entry.value) return true;
    }
    return false;
}

// Force a single δ-unfold of an opaque-Definition head, if the expression
// has one. Returns the unfolded term (the definition's body, re-applied to
// the spine arguments) or nullptr when the head is not an opaque definition.
//
// Used ONLY by isDefinitionallyEqual's opacity-tolerant fallback. Opacity
// stops δ-unfolding during general `weakHeadNormalForm`, so a goal like
// `x ≤ z` stays at `IsNonneg(z - x)` rather than blowing through to its
// `Quotient.lift` implementation — that shape preservation is what the
// rewrite engine and the auto-prover's syntactic matchers rely on. But an
// opaque constant is still a genuine definition, so a term headed by it is
// definitionally equal to its unfolding. When a leaf comparison has otherwise
// failed, retrying with the opaque head made transparent recovers that
// equality. This is a single, local unfold at exactly the spot the surface
// `unfold X in …` form used to mark by hand — never during general WHNF.
ExpressionPointer unfoldOpaqueHeadOnce(const Environment& environment,
                                       const ExpressionPointer& expression) {
    auto spine = peelApplicationSpine(expression);
    auto* constant = std::get_if<Constant>(&spine.head->node);
    if (!constant) return nullptr;
    auto* declaration = environment.lookup(constant->name);
    auto* definition =
        declaration ? std::get_if<Definition>(declaration) : nullptr;
    if (!definition || definition->opacity != Opacity::Opaque) {
        return nullptr;
    }
    // Opaque VALUE definitions are hard: refuse even the demand-point retry —
    // only an explicit `unfold X in …` may see through one. Quotient-type
    // aliases are soft (see isHardOpaqueConstant).
    if (isHardOpaqueConstant(environment, constant->name)) {
        return nullptr;
    }
    if (definition->universeParameters.size()
            != constant->universeArguments.size()) {
        return nullptr;
    }
    auto body = definition->body;
    if (!definition->universeParameters.empty()) {
        body = substituteUniverseLevels(
            body, definition->universeParameters, constant->universeArguments);
    }
    return applyArguments(body, spine.args);
}

// Inner implementation. The public wrapper below handles the positive-
// result cache and the step counter; this function does the actual
// equality work. Fuel decrement happens here so the cache lookup itself
// doesn't burn fuel (positive cache hits truly are free).
bool isDefinitionallyEqualImpl(const Environment& environment,
                               const Context& context,
                               ExpressionPointer left,
                               ExpressionPointer right,
                               int fuel) {
    if (--fuel <= 0) {
        // Conservative on exhaustion: don't claim equality we can't prove.
        return false;
    }
    // Pointer-identity short-circuit. Subexpressions show up repeatedly
    // in calc chains and `congruenceOf` lambdas; every time we compare
    // a function applied at two different arguments we end up recursing
    // into the *same* function expression on both sides, which is the
    // same shared_ptr. Skipping the WHNF + structural recurse for those
    // is the single biggest savings on heavy quotient proofs.
    if (left.get() == right.get()) {
        return true;
    }
    // Cheap allocation-free structural check before reducing. Bounded by
    // expression depth and prunes whenever we hit a shared subtree, so
    // it's never more work than the post-WHNF structural recurse below
    // — and on already-equal terms it lets us skip the WHNF allocations
    // entirely.
    if (structurallyEqual(left, right)) {
        return true;
    }
    // δ-reduce let-bound FreeVariables in both sides so the kernel sees
    // through surface `let X := V` abbreviations. The walk is a no-op
    // when the context has no let-binders (every existing call site).
    left  = deltaReduceLetFreeVariables(std::move(left),  context);
    right = deltaReduceLetFreeVariables(std::move(right), context);
    auto leftReduced  = weakHeadNormalForm(environment, std::move(left),  fuel);
    auto rightReduced = weakHeadNormalForm(environment, std::move(right), fuel);
    // Same fast-paths after WHNF — reductions often produce the same
    // shared term when both inputs go through the same path.
    if (leftReduced.get() == rightReduced.get()) {
        return true;
    }
    if (structurallyEqual(leftReduced, rightReduced)) {
        return true;
    }

    // NaturalLiteral bridging (PLAN_FAST_NUMERALS §B): a literal is
    // defeq-interchangeable with its constructor form. Two literals are
    // equal exactly when their values agree — the structural check above
    // already accepted equal values, so reaching here means unequal.
    // A literal against a `zero` is its zero test; against a
    // `successor`-headed term the constructor is peeled INLINE and the
    // comparison recurses on (value-1, successor's argument). The peel
    // must not go through naturalLiteralConstructorView + a general
    // recursion: WHNF would eagerly re-compact `successor(lit(n-1))`
    // back to `lit(n)` and the comparison would loop. Anything else
    // genuinely differs (a Natural lives in Type 0, so no later
    // fallback can apply).
    {
        auto* leftLiteral  = std::get_if<NaturalLiteral>(&leftReduced->node);
        auto* rightLiteral = std::get_if<NaturalLiteral>(&rightReduced->node);
        if (leftLiteral && rightLiteral) {
            return false;
        }
        auto compareLiteralAgainst =
            [&](const NaturalValue& value,
                const ExpressionPointer& other) -> std::optional<bool> {
            if (auto* constant = std::get_if<Constant>(&other->node)) {
                if (constant->name == "zero"
                    && isNaturalConstructor(environment, "zero")) {
                    return value == 0;
                }
                return std::nullopt;
            }
            if (auto* application = std::get_if<Application>(&other->node)) {
                auto* head =
                    std::get_if<Constant>(&application->function->node);
                if (head && head->name == "successor"
                    && isNaturalConstructor(environment, "successor")) {
                    if (value == 0) return false;
                    return isDefinitionallyEqual(
                        environment, context,
                        makeNaturalLiteral(value - 1),
                        application->argument, fuel);
                }
            }
            return std::nullopt;
        };
        if (leftLiteral) {
            if (auto verdict = compareLiteralAgainst(
                    leftLiteral->value, rightReduced)) {
                return *verdict;
            }
        }
        if (rightLiteral) {
            if (auto verdict = compareLiteralAgainst(
                    rightLiteral->value, leftReduced)) {
                return *verdict;
            }
        }
    }

    // Structural cases. When recursing into a Pi or Lambda body/codomain,
    // we *open* the binder with a fresh free variable and extend the
    // context with that variable's type, so the comparison context tracks
    // every variable in scope. This is what makes proof irrelevance below
    // able to call inferType on subterms.
    if (auto* leftBound = std::get_if<BoundVariable>(&leftReduced->node)) {
        auto* rightBound = std::get_if<BoundVariable>(&rightReduced->node);
        if (rightBound &&
            leftBound->deBruijnIndex == rightBound->deBruijnIndex) {
            return true;
        }
    } else if (auto* leftFree = std::get_if<FreeVariable>(&leftReduced->node)) {
        auto* rightFree = std::get_if<FreeVariable>(&rightReduced->node);
        if (rightFree && leftFree->name == rightFree->name
                      && leftFree->origin == rightFree->origin) {
            return true;
        }
    } else if (auto* leftSort = std::get_if<Sort>(&leftReduced->node)) {
        auto* rightSort = std::get_if<Sort>(&rightReduced->node);
        if (rightSort && levelsDefinitionallyEqual(leftSort->level,
                                                   rightSort->level)) {
            return true;
        }
    } else if (auto* leftConstant = std::get_if<Constant>(&leftReduced->node)) {
        // After weakHeadNormalForm, a Constant at the head can only be an
        // Axiom / Inductive / Constructor / Recursor (Definitions were
        // unfolded). Two such constants are equal iff they have the same
        // name AND the same universe arguments — distinct universe
        // instantiations of a polymorphic constant are NOT interchangeable.
        if (auto* rightConstant = std::get_if<Constant>(&rightReduced->node);
            rightConstant && leftConstant->name == rightConstant->name &&
            leftConstant->universeArguments.size()
                == rightConstant->universeArguments.size()) {
            bool allLevelsAgree = true;
            for (std::size_t i = 0;
                 i < leftConstant->universeArguments.size(); ++i) {
                if (!levelsDefinitionallyEqual(
                        leftConstant->universeArguments[i],
                        rightConstant->universeArguments[i])) {
                    allLevelsAgree = false;
                    break;
                }
            }
            if (allLevelsAgree) return true;
        }
    } else if (auto* leftPi = std::get_if<Pi>(&leftReduced->node)) {
        if (auto* rightPi = std::get_if<Pi>(&rightReduced->node)) {
            if (!isDefinitionallyEqual(environment, context,
                                       leftPi->domain, rightPi->domain, fuel)) {
                return false;
            }
            auto fresh = makeOpeningName(context);
            Context extendedContext = context;
            extendedContext.push_back(
                {fresh, leftPi->domain, FreeVariableOrigin::Internal});
            return isDefinitionallyEqual(
                environment, extendedContext,
                openBinder(leftPi->codomain,  fresh, FreeVariableOrigin::Internal),
                openBinder(rightPi->codomain, fresh, FreeVariableOrigin::Internal),
                fuel);
        }
    } else if (auto* leftLambda = std::get_if<Lambda>(&leftReduced->node)) {
        if (auto* rightLambda = std::get_if<Lambda>(&rightReduced->node)) {
            if (!isDefinitionallyEqual(environment, context,
                                       leftLambda->domain,
                                       rightLambda->domain, fuel)) {
                return false;
            }
            auto fresh = makeOpeningName(context);
            Context extendedContext = context;
            extendedContext.push_back(
                {fresh, leftLambda->domain, FreeVariableOrigin::Internal});
            return isDefinitionallyEqual(
                environment, extendedContext,
                openBinder(leftLambda->body,  fresh, FreeVariableOrigin::Internal),
                openBinder(rightLambda->body, fresh, FreeVariableOrigin::Internal),
                fuel);
        }
    } else if (auto* leftApplication = std::get_if<Application>(&leftReduced->node)) {
        if (auto* rightApplication = std::get_if<Application>(&rightReduced->node)) {
            if (isDefinitionallyEqual(environment, context,
                                      leftApplication->function,
                                      rightApplication->function, fuel)
             && isDefinitionallyEqual(environment, context,
                                      leftApplication->argument,
                                      rightApplication->argument, fuel)) {
                return true;
            }
            // Otherwise fall through — proof irrelevance might still apply.
        }
    }

    // η-conversion: λx. f x  ≡  f  (when x is not free in f). If exactly
    // one side is a Lambda, η-expand the other and compare.
    {
        auto* leftLambda  = std::get_if<Lambda>(&leftReduced->node);
        auto* rightLambda = std::get_if<Lambda>(&rightReduced->node);
        if (leftLambda && !rightLambda) {
            auto etaExpandedRight = makeApplication(
                shift(rightReduced, 1), makeBoundVariable(0));
            auto fresh = makeOpeningName(context);
            Context extendedContext = context;
            extendedContext.push_back(
                {fresh, leftLambda->domain, FreeVariableOrigin::Internal});
            if (isDefinitionallyEqual(
                    environment, extendedContext,
                    openBinder(leftLambda->body, fresh, FreeVariableOrigin::Internal),
                    openBinder(etaExpandedRight, fresh, FreeVariableOrigin::Internal),
                    fuel)) {
                return true;
            }
        }
        if (rightLambda && !leftLambda) {
            auto etaExpandedLeft = makeApplication(
                shift(leftReduced, 1), makeBoundVariable(0));
            auto fresh = makeOpeningName(context);
            Context extendedContext = context;
            extendedContext.push_back(
                {fresh, rightLambda->domain, FreeVariableOrigin::Internal});
            if (isDefinitionallyEqual(
                    environment, extendedContext,
                    openBinder(etaExpandedLeft, fresh, FreeVariableOrigin::Internal),
                    openBinder(rightLambda->body, fresh, FreeVariableOrigin::Internal),
                    fuel)) {
                return true;
            }
        }
    }

    // Proof irrelevance: any two terms whose type lives in Proposition are
    // definitionally equal. We infer the types and check whether their
    // kind (the type of the type) is Sort 0 (= Proposition).
    try {
        auto leftType = inferType(environment, context, leftReduced);
        auto leftKind = weakHeadNormalForm(
            environment, inferType(environment, context, leftType), fuel);
        if (auto* sort = std::get_if<Sort>(&leftKind->node)) {
            auto concreteLevel = levelAsConstant(sort->level);
            if (concreteLevel && *concreteLevel == 0) {
                // leftReduced is a proof of leftType, a proposition.
                auto rightType = inferType(environment, context, rightReduced);
                if (isDefinitionallyEqual(environment, context,
                                          leftType, rightType, fuel)) {
                    return true;
                }
            }
        }
    } catch (const TypeError&) {
        // One side isn't well-typed in this context — skip irrelevance.
    }

    // Opacity-tolerant fallback (see unfoldOpaqueHeadOnce). If either side
    // is still headed by an opaque definition after WHNF and the structural
    // comparison failed, the two terms may differ only by that definition's
    // unfolding. Retry the comparison with the opaque head made transparent —
    // a single, local transparency that mirrors the manual `unfold` wrap's
    // scope without disturbing the shape-preserving general WHNF.
    if (auto unfoldedLeft = unfoldOpaqueHeadOnce(environment, leftReduced)) {
        if (isDefinitionallyEqual(environment, context,
                                  unfoldedLeft, rightReduced, fuel)) {
            return true;
        }
    }
    if (auto unfoldedRight = unfoldOpaqueHeadOnce(environment, rightReduced)) {
        if (isDefinitionallyEqual(environment, context,
                                  leftReduced, unfoldedRight, fuel)) {
            return true;
        }
    }

    return false;
}

} // namespace

bool isDefinitionallyEqual(const Environment& environment,
                           const Context& context,
                           ExpressionPointer left,
                           ExpressionPointer right,
                           int fuel) {
    ++isDefEqCallCount;
    kernelStep("isDefEq", left, right);
    // ζ-reduce let-bound FreeVariables up-front so the cache key is
    // context-independent. With it inside the body, two calls with the
    // same expressions but different let-contexts would compute different
    // answers — but if we substitute the let values into the keys here,
    // the keys themselves carry the context's relevant content. (For
    // contexts without let-binders, this is a no-op.)
    if (kernelCacheEnabled && contextHasLetBinders(context)) {
        left  = deltaReduceLetFreeVariables(std::move(left),  context);
        right = deltaReduceLetFreeVariables(std::move(right), context);
    }
    // Positive-result cache lookup. We cache only TRUE results (a `false`
    // may have been a fuel-exhaustion conservative answer; reusing it
    // elsewhere with more fuel would be unsound).
    const bool useCache = kernelCacheEnabled;
    ReductionDepthGuard depthGuard;
    std::pair<ExpressionPointer, ExpressionPointer> cacheKey{left, right};
    if (useCache) {
        ensureKernelCacheOwner(environment);
        if (isDefEqTrueCache.find(cacheKey) != isDefEqTrueCache.end()) {
            ++isDefEqCacheHits;
            return true;
        }
    }
    {
        // Loop detection runs regardless of result caching (see the WHNF
        // wrapper: a cycle would otherwise recurse to stack overflow).
        // Re-entering an equality comparison that's already on the
        // stack means descent didn't make progress. Bail out with
        // `false`; the outer comparison will then try its other
        // strategies (η, proof irrelevance) which may still resolve it.
        if (isDefEqInFlight.find(cacheKey) != isDefEqInFlight.end()) {
            ++isDefEqLoopsDetected;
            ++loopShortCircuitEpoch;
            return false;
        }
        ++isDefEqCacheMisses;
        isDefEqInFlight.insert(cacheKey);
    }
    uint64_t epochBefore = loopShortCircuitEpoch;
    bool answer;
    try {
        answer = isDefinitionallyEqualImpl(
            environment, context, std::move(left), std::move(right), fuel);
    } catch (const KernelResourceExhausted&) {
        // A reduction at some position exhausted its depth/fuel budget
        // before we could decide equality. Conservatively answer `false`
        // ("can't tell, assume not equal") rather than propagating: a
        // `false` is always sound (acceptance needs `true`), and it lets
        // callers — coercion, the calc diff-walk — fall through to their
        // structural strategies instead of aborting the whole elaboration
        // on a heavy subterm at a non-matching position. Not cached
        // (matching the fuel-exhaustion contract: a conservative `false`
        // must never be reused as if it were a decided answer).
        isDefEqInFlight.erase(cacheKey);
        return false;
    } catch (...) {
        isDefEqInFlight.erase(cacheKey);
        throw;
    }
    isDefEqInFlight.erase(cacheKey);
    if (useCache) {
        // A `true` reached through a loop-detection short-circuit below us
        // is stack-dependent (see loopShortCircuitEpoch) — don't memoise.
        if (answer && loopShortCircuitEpoch == epochBefore)
            isDefEqTrueCache.insert(cacheKey);
    }
    // Diagnostic (MATH_DEFEQ_POISON_CHECK=1): a top-level `false` is
    // re-tried with all caches cleared; a flip to `true` proves a cache
    // entry poisoned the comparison.
    if (!answer && useCache && isDefEqInFlight.empty()
        && std::getenv("MATH_DEFEQ_POISON_CHECK")) {
        whnfCache.clear();
        isDefEqTrueCache.clear();
        whnfInFlight.clear();
        bool fresh = false;
        try {
            fresh = isDefinitionallyEqualImpl(
                environment, context, cacheKey.first, cacheKey.second, fuel);
        } catch (...) {
            fresh = false;
        }
        if (fresh) {
            std::fprintf(stderr,
                "[defeq-poison] cached answer false, fresh answer true\n"
                "  left:  %s\n  right: %s\n",
                renderForDiagnostic(cacheKey.first).c_str(),
                renderForDiagnostic(cacheKey.second).c_str());
            return true;
        }
    }
    return answer;
}

// (`isSubtype` was removed when the kernel adopted Lean 4's non-cumulative
// universe convention. It used to accept `Sort m <: Sort n` for m <= n
// (cumulativity) with a covariant-Pi codomain; with cumulativity gone its
// Sort case required level EQUALITY, at which point it was observationally
// identical to `isDefinitionallyEqual`. The three call sites — Application
// argument checks, Let value checks, and the addDefinition body check —
// now call `isDefinitionallyEqual` directly. See PLAN_KERNEL.md §4.3.)

std::string freshName(const std::string& displayHint, const Context& context) {
    auto isInUse = [&](const std::string& candidate) {
        for (const auto& entry : context) {
            if (entry.name == candidate) return true;
        }
        return false;
    };
    std::string base = displayHint.empty() ? "x" : displayHint;
    if (!isInUse(base)) return base;
    for (int suffix = 1;; ++suffix) {
        auto candidate = base + "_" + std::to_string(suffix);
        if (!isInUse(candidate)) return candidate;
    }
}

namespace {
ExpressionPointer inferTypeWork(const Environment& environment,
                                const Context& context,
                                ExpressionPointer expression);
}

ExpressionPointer inferType(const Environment& environment,
                            const Context& context,
                            ExpressionPointer expression) {
    // Cache lookup. The key is (expression structural hash, context
    // fingerprint). On hit, verify the cached entry's expression is
    // structurally equal — guards against hash collisions on key collisions.
    // The fingerprint is computed once per top-level inferType call; the
    // recursive sub-calls each recompute their own (cheap, O(N) in context
    // size). For most call shapes the context size is small.
    static const bool inferCacheDisabled = [] {
        const char* f = std::getenv("MATH_DISABLE_INFER_TYPE_CACHE");
        return f && f[0] != '\0' && f[0] != '0';
    }();
    InferTypeCacheKey key;
    if (!inferCacheDisabled) {
        ensureKernelCacheOwner(environment);
        key.expressionHash = expression ? expression->hash : 0;
        key.contextFingerprint = contextFingerprint(context);
        auto range = inferTypeCache.equal_range(key);
        for (auto it = range.first; it != range.second; ++it) {
            if (structurallyEqual(it->second.expression, expression)) {
                ++inferTypeCacheHits;
                return it->second.type;
            }
        }
        ++inferTypeCacheMisses;
    }
    if (!kernelCheckInvariants || isCurrentlyCheckingInvariants) {
        ExpressionPointer result = inferTypeWork(environment, context, expression);
        if (!inferCacheDisabled) {
            inferTypeCache.emplace(key, InferTypeCacheValue{expression, result});
        }
        return result;
    }
    isCurrentlyCheckingInvariants = true;
    ExpressionPointer result;
    try {
        result = inferTypeWork(environment, context, expression);
        // Kind soundness: re-infer the result type and require it to be a
        // Sort. The recursive call sees isCurrentlyCheckingInvariants set
        // and takes the fast path, so the check itself doesn't recurse.
        auto kind = weakHeadNormalForm(
            environment, inferType(environment, context, result));
        if (!std::holds_alternative<Sort>(kind->node)) {
            isCurrentlyCheckingInvariants = false;
            throw TypeError(
                "invariant violation: inferType returned an internally "
                "ill-formed type (its own kind did not reduce to a Sort)");
        }
    } catch (...) {
        isCurrentlyCheckingInvariants = false;
        throw;
    }
    isCurrentlyCheckingInvariants = false;
    if (!inferCacheDisabled) {
        inferTypeCache.emplace(key, InferTypeCacheValue{expression, result});
    }
    return result;
}

namespace {
ExpressionPointer inferTypeWork(const Environment& environment,
                                const Context& context,
                                ExpressionPointer expression) {
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        std::string message =
            "internal: bare BoundVariable reached inferType (index " +
            std::to_string(boundVariable->deBruijnIndex) +
            "); binders should be opened before recursing";
        if (!context.empty()) {
            message += " (context has";
            for (const auto& entry : context) {
                message += " ";
                message +=
                    entry.origin == FreeVariableOrigin::Internal ? "@" : "";
                message += entry.name;
            }
            message += ")";
        } else {
            message += " (empty context)";
        }
        throw TypeError(message);
    }
    if (auto* freeVariable = std::get_if<FreeVariable>(&expression->node)) {
        for (auto entry = context.rbegin(); entry != context.rend(); ++entry) {
            if (entry->name == freeVariable->name &&
                entry->origin == freeVariable->origin) {
                return entry->type;
            }
        }
        // Build a diagnostic that lists what was in scope so the
        // caller can see whether the variable is truly missing or
        // present under a different origin (User vs Internal — a
        // common confusion when an elaborator desugar mixes opened
        // and closed sub-expressions).
        std::string message =
            std::string(freeVariable->origin == FreeVariableOrigin::User
                            ? "unbound free variable: "
                            : "unbound internal variable: ")
            + freeVariable->name;
        if (context.empty()) {
            message += " (context is empty)";
        } else {
            message += " (in-scope:";
            for (const auto& entry : context) {
                message += " ";
                message +=
                    entry.origin == FreeVariableOrigin::Internal ? "@" : "";
                message += entry.name;
            }
            message += ")";
        }
        throw TypeError(message);
    }
    if (auto* constant = std::get_if<Constant>(&expression->node)) {
        auto* declaration = environment.lookup(constant->name);
        if (!declaration) {
            throw TypeError("undefined constant: " + constant->name);
        }
        const auto& parameters = declarationUniverseParameters(*declaration);
        if (parameters.size() != constant->universeArguments.size()) {
            throw TypeError(
                "constant " + constant->name + ": expected " +
                std::to_string(parameters.size()) +
                " universe argument(s), got " +
                std::to_string(constant->universeArguments.size()));
        }
        auto type = declarationType(*declaration);
        if (!parameters.empty()) {
            type = substituteUniverseLevels(type, parameters,
                                            constant->universeArguments);
        }
        return type;
    }
    if (auto* sort = std::get_if<Sort>(&expression->node)) {
        return makeSort(makeLevelSuccessor(sort->level));
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        auto domainKind = weakHeadNormalForm(
            environment, inferType(environment, context, pi->domain));
        auto* domainSort = std::get_if<Sort>(&domainKind->node);
        if (!domainSort) {
            TypeError error("Pi: domain is not a type");
            error.actualType = domainKind;
            throw error;
        }
        auto introducedName = freshName(pi->displayHint, context);
        Context extendedContext = context;
        extendedContext.push_back({introducedName, pi->domain});
        auto codomainKind = weakHeadNormalForm(
            environment,
            inferType(environment, extendedContext,
                      openBinder(pi->codomain, introducedName)));
        auto* codomainSort = std::get_if<Sort>(&codomainKind->node);
        if (!codomainSort) {
            TypeError error("Pi: codomain is not a type");
            error.actualType = codomainKind;
            throw error;
        }
        return makeSort(
            impredicativeMaxLevel(domainSort->level, codomainSort->level));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        auto domainKind = weakHeadNormalForm(
            environment, inferType(environment, context, lambda->domain));
        if (!std::holds_alternative<Sort>(domainKind->node)) {
            TypeError error("Lambda: domain is not a type");
            error.actualType = domainKind;
            throw error;
        }
        auto introducedName = freshName(lambda->displayHint, context);
        Context extendedContext = context;
        extendedContext.push_back({introducedName, lambda->domain});
        auto bodyType = inferType(environment, extendedContext,
                                  openBinder(lambda->body, introducedName));
        return makePi(lambda->displayHint,
                      lambda->domain,
                      closeBinder(bodyType, introducedName));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        auto functionType = weakHeadNormalForm(
            environment,
            inferType(environment, context, application->function));
        auto* functionAsPi = std::get_if<Pi>(&functionType->node);
        if (!functionAsPi) {
            // Opacity-tolerant retry: the function's type may be headed by an
            // opaque definition whose unfolding IS a Pi (e.g. applying a value
            // of opaque `IsNonneg(x)`, which unfolds through `Quotient.lift`
            // to a `∀ ε. …` Pi). Opacity blocks this during general WHNF to
            // keep goal shape; here, where a Pi is genuinely demanded, force
            // the opaque head transparent and re-reduce. Mirrors the defeq
            // bridge (see unfoldOpaqueHeadOnce).
            if (auto unfolded = unfoldOpaqueHeadOnce(environment, functionType)) {
                functionType = weakHeadNormalForm(environment, unfolded);
                functionAsPi = std::get_if<Pi>(&functionType->node);
            }
        }
        if (!functionAsPi) {
            TypeError error("Application: function is not of Pi type");
            error.actualType = functionType;
            throw error;
        }
        auto argumentType = inferType(environment, context, application->argument);
        if (!isDefinitionallyEqual(environment, context, argumentType,
                                   functionAsPi->domain)) {
            TypeError error("Application: argument type does not match Pi domain");
            error.expectedType = functionAsPi->domain;
            error.actualType = argumentType;
            error.offendingFunction = application->function;
            error.offendingArgument = application->argument;
            throw error;
        }
        return substitute(functionAsPi->codomain, 0, application->argument);
    }
    if (std::holds_alternative<NaturalLiteral>(expression->node)) {
        if (environment.lookup("Natural") == nullptr) {
            throw TypeError(
                "natural literal: the inductive `Natural` is not declared "
                "in this environment (import Natural.basics)");
        }
        return makeConstant("Natural");
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        // Check the declared type is itself a type.
        auto kindOfType = weakHeadNormalForm(
            environment, inferType(environment, context, let->type));
        if (!std::holds_alternative<Sort>(kindOfType->node)) {
            TypeError error("Let: declared type is not a type");
            error.actualType = kindOfType;
            throw error;
        }
        // Check the value's inferred type matches the declared type.
        auto inferredValueType = inferType(environment, context, let->value);
        if (!isDefinitionallyEqual(environment, context, inferredValueType,
                                   let->type)) {
            TypeError error("Let: value type does not match declared type");
            error.expectedType = let->type;
            error.actualType = inferredValueType;
            throw error;
        }
        // Substitute the value into the body and infer that.
        return inferType(environment, context,
                         substitute(let->body, 0, let->value));
    }
    throw TypeError("internal: unhandled Expression variant in inferType");
}
} // namespace

uint64_t kernelAddDeclMicros = 0;
uint64_t kernelAddDeclCount = 0;

void addAxiom(Environment& environment,
              std::string name,
              std::vector<std::string> universeParameters,
              ExpressionPointer declaredType, bool automatic) {
    validateName(name, "addAxiom: axiom name");
    for (const auto& parameterName : universeParameters) {
        validateName(parameterName, "addAxiom: universe parameter name");
    }
    if (environment.declarations.count(name)) {
        throw TypeError("addAxiom: name already declared: " + name);
    }
    KernelInstrumentationScope instrumentationScope("axiom " + name);
    long long t0 = monotonicNanos();
    auto kindOfType = weakHeadNormalForm(
        environment, inferType(environment, {}, declaredType));
    long long t1 = monotonicNanos();
    kernelAddDeclMicros += (t1 - t0) / 1000;
    ++kernelAddDeclCount;
    if (!std::holds_alternative<Sort>(kindOfType->node)) {
        throw TypeError("addAxiom: declared type is not a type for " + name);
    }
    environment.declarations.emplace(
        std::move(name),
        Axiom{std::move(universeParameters), std::move(declaredType),
              automatic});
}

void addDefinition(Environment& environment,
                   std::string name,
                   std::vector<std::string> universeParameters,
                   ExpressionPointer declaredType,
                   ExpressionPointer body,
                   Opacity opacity, bool automatic) {
    validateName(name, "addDefinition: definition name");
    for (const auto& parameterName : universeParameters) {
        validateName(parameterName, "addDefinition: universe parameter name");
    }
    if (environment.declarations.count(name)) {
        throw TypeError("addDefinition: name already declared: " + name);
    }
    KernelInstrumentationScope instrumentationScope("definition " + name);
    long long t0 = monotonicNanos();
    auto kindOfType = weakHeadNormalForm(
        environment, inferType(environment, {}, declaredType));
    if (!std::holds_alternative<Sort>(kindOfType->node)) {
        throw TypeError(
            "addDefinition: declared type is not a type for " + name);
    }
    auto inferredBodyType = inferType(environment, {}, body);
    if (!isDefinitionallyEqual(environment, {}, inferredBodyType,
                               declaredType)) {
        TypeError error(
            "addDefinition: body type does not match declared type for " + name);
        error.expectedType = declaredType;
        error.actualType = inferredBodyType;
        throw error;
    }
    long long t1 = monotonicNanos();
    kernelAddDeclMicros += (t1 - t0) / 1000;
    ++kernelAddDeclCount;
    environment.declarations.emplace(
        std::move(name),
        Definition{std::move(universeParameters),
                   std::move(declaredType), std::move(body),
                   opacity, automatic});
}

namespace {

// True if `expression` syntactically contains a Constant with the given
// name anywhere. Used by the strict-positivity check below — and only by
// it; it's a cheap structural walk, not a semantic test.
bool mentionsConstant(ExpressionPointer expression,
                      const std::string& constantName) {
    if (auto* c = std::get_if<Constant>(&expression->node)) {
        return c->name == constantName;
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return mentionsConstant(pi->domain,   constantName)
            || mentionsConstant(pi->codomain, constantName);
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return mentionsConstant(lambda->domain, constantName)
            || mentionsConstant(lambda->body,   constantName);
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return mentionsConstant(application->function, constantName)
            || mentionsConstant(application->argument, constantName);
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return mentionsConstant(let->type,  constantName)
            || mentionsConstant(let->value, constantName)
            || mentionsConstant(let->body,  constantName);
    }
    return false;  // BoundVariable, FreeVariable, Sort: no Constant inside.
}

// Strict positivity: the inductive type's name may appear in constructor
// argument types only in "strictly positive" positions. Concretely:
//   - it may appear nowhere (a non-recursive argument), OR
//   - the type may be `T params indices` — an Application chain whose
//     head is the inductive's Constant — provided T doesn't appear in
//     any of those arguments (no nested inductives). This catches
//     direct recursive args like (List A) for List.prepend.
//   - the type may be Π(_ : A). B where A doesn't mention T and B is
//     strictly positive in T (higher-order recursive arg, like
//     mkInfTree : (Nat → Tree) → Tree).
// The rule rejects pathological declarations like
//   Bad : Type 0 := mkBad : (Bad → Bool) → Bad.
bool isStrictlyPositive(ExpressionPointer expression,
                        const std::string& inductiveName) {
    if (!mentionsConstant(expression, inductiveName)) return true;
    // Peel an Application chain to find the head.
    auto head = expression;
    while (auto* application = std::get_if<Application>(&head->node)) {
        head = application->function;
    }
    if (auto* c = std::get_if<Constant>(&head->node);
        c && c->name == inductiveName) {
        // Direct (or parameterised) recursive use. Require that the
        // arguments themselves don't mention the inductive — we don't
        // yet support nested inductive recursion (e.g. List (List A)
        // as a constructor argument would need a more refined check).
        auto walker = expression;
        while (auto* application = std::get_if<Application>(&walker->node)) {
            if (mentionsConstant(application->argument, inductiveName)) {
                return false;
            }
            walker = application->function;
        }
        return true;
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return !mentionsConstant(pi->domain, inductiveName)
            && isStrictlyPositive(pi->codomain, inductiveName);
    }
    return false;
}

// Verifies that every argument of `constructor` is strictly positive in
// `inductiveName`. Walks the constructor's type as a Pi-chain. Returns the
// codomain-after-stripping (the conclusion of the constructor) so the
// caller can also check it ends in the inductive.
ExpressionPointer checkConstructorStrictlyPositive(
    const std::string& inductiveName,
    const ConstructorSpec& constructor) {
    auto walker = constructor.type;
    int argumentIndex = 0;
    while (auto* pi = std::get_if<Pi>(&walker->node)) {
        if (!isStrictlyPositive(pi->domain, inductiveName)) {
            throw TypeError(
                "addInductive: constructor " + constructor.name +
                " argument " + std::to_string(argumentIndex) +
                " has non-strictly-positive occurrence of " + inductiveName);
        }
        // Walk into the codomain. The codomain may reference the bound
        // variable via BoundVariable(0); we don't need to track it for
        // the positivity check (we only inspect each Pi's domain), but
        // we must advance through the binder structure.
        walker = pi->codomain;
        argumentIndex++;
    }
    return walker;
}

// Generalised recursor builder, with parameter and index support. Every
// binder in the recursor's type is named with an Internal-origin free
// variable during construction; closeBinder turns those back into bound
// variables in the right order.

// Information about one binder appearing in the inductive's kind: its
// fresh free-variable name (used during construction), its display hint,
// its domain (in the context of preceding binders, with FreeVariables for
// each), and whether it is a parameter or an index.
struct KindBinderInfo {
    std::string freshName;
    std::string displayHint;
    ExpressionPointer type;
    bool isParameter;
};

// Walks the inductive's kind, returning a binder for each Pi and the
// terminal Sort (which lives in the context of all binders, with
// FreeVariables substituted for each Pi-bound variable).
struct SplitKind {
    std::vector<KindBinderInfo> binders;
    ExpressionPointer terminalSort;
};
SplitKind splitInductiveKind(ExpressionPointer kind, int numParameters) {
    SplitKind result;
    auto walker = kind;
    int piIndex = 0;
    while (auto* pi = std::get_if<Pi>(&walker->node)) {
        std::string freshName = "indBinder_" + std::to_string(piIndex);
        result.binders.push_back({
            freshName, pi->displayHint, pi->domain,
            piIndex < numParameters});
        walker = openBinder(pi->codomain, freshName,
                            FreeVariableOrigin::Internal);
        piIndex++;
    }
    result.terminalSort = walker;
    return result;
}

// Builds the case type for one constructor in the recursor's signature.
// The case binds each non-parameter argument of the constructor; for each
// recursive argument (one whose type is the inductive applied to params
// and some indices), an extra hypothesis binder is inserted that gives
// access to the inductive hypothesis. The case's conclusion is
// `motive constructorIndices (constructor params nonParamArgs)` where
// constructorIndices are the specific indices the constructor produces.
//
// The constructor's first numParameters Pis are opened with the SAME
// fresh names that the recursor builder uses for the inductive's
// parameters, so references to the parameters inside the case type live
// in the same name space as the rest of the recursor.
ExpressionPointer buildCaseType(
    const std::string& inductiveName,
    const std::vector<LevelPointer>& inductiveUniverseArgs,
    const std::vector<KindBinderInfo>& inductiveBinders,
    int numParameters,
    const std::string& motivePlaceholder,
    const ConstructorSpec& constructor) {
    auto walker = constructor.type;

    // Open the constructor's parameter prefix with the inductive's
    // parameter fresh names.
    for (int p = 0; p < numParameters; ++p) {
        auto* pi = std::get_if<Pi>(&walker->node);
        if (!pi) {
            throw TypeError(
                "buildCaseType: constructor " + constructor.name +
                " has fewer Pi binders than the inductive's "
                "parameter count");
        }
        walker = openBinder(pi->codomain, inductiveBinders[p].freshName,
                            FreeVariableOrigin::Internal);
    }

    struct NonParamArg {
        std::string freshName;
        std::string displayHint;
        ExpressionPointer type;
        bool isRecursive;
        std::vector<ExpressionPointer> indicesForRecursiveCall;
    };
    std::vector<NonParamArg> nonParamArgs;
    int nonParamIndex = 0;
    while (auto* pi = std::get_if<Pi>(&walker->node)) {
        std::string freshName = "ctorArg_" + std::to_string(nonParamIndex);

        // Determine if this argument is a (direct) recursive argument by
        // peeling its type's Application chain. A recursive argument's
        // type is `T params indices` for some indices.
        bool isRecursive = false;
        std::vector<ExpressionPointer> recursiveIndices;
        auto typeHead = pi->domain;
        std::vector<ExpressionPointer> typeArgs;
        while (auto* app = std::get_if<Application>(&typeHead->node)) {
            typeArgs.push_back(app->argument);
            typeHead = app->function;
        }
        std::reverse(typeArgs.begin(), typeArgs.end());
        if (auto* c = std::get_if<Constant>(&typeHead->node);
            c && c->name == inductiveName &&
            (int)typeArgs.size() == (int)inductiveBinders.size()) {
            isRecursive = true;
            for (std::size_t i = numParameters; i < typeArgs.size(); ++i) {
                recursiveIndices.push_back(typeArgs[i]);
            }
        }

        nonParamArgs.push_back({
            freshName, pi->displayHint, pi->domain,
            isRecursive, recursiveIndices});
        walker = openBinder(pi->codomain, freshName,
                            FreeVariableOrigin::Internal);
        nonParamIndex++;
    }

    // The walker is now the conclusion `T params constructorIndices`.
    // Peel its Application chain to extract the index values.
    std::vector<ExpressionPointer> conclusionArgs;
    auto conclusionHead = walker;
    while (auto* app = std::get_if<Application>(&conclusionHead->node)) {
        conclusionArgs.push_back(app->argument);
        conclusionHead = app->function;
    }
    std::reverse(conclusionArgs.begin(), conclusionArgs.end());
    std::vector<ExpressionPointer> constructorIndices;
    for (std::size_t i = numParameters; i < conclusionArgs.size(); ++i) {
        constructorIndices.push_back(conclusionArgs[i]);
    }

    // Innermost body: motive constructorIndices (constructor params args).
    auto constructorApplied =
        makeConstant(constructor.name, inductiveUniverseArgs);
    for (int p = 0; p < numParameters; ++p) {
        constructorApplied = makeApplication(
            constructorApplied,
            makeInternalFreeVariable(inductiveBinders[p].freshName));
    }
    for (const auto& argument : nonParamArgs) {
        constructorApplied = makeApplication(
            constructorApplied,
            makeInternalFreeVariable(argument.freshName));
    }
    auto body = makeInternalFreeVariable(motivePlaceholder);
    for (const auto& idx : constructorIndices) {
        body = makeApplication(body, idx);
    }
    body = makeApplication(body, constructorApplied);

    // Wrap the minor premise in Lean's layout: the constructor's value
    // arguments first, then one inductive-hypothesis Pi per recursive
    // argument, in argument order — an external checker re-derives
    // recursors in exactly this shape (PLAN_KERNEL_EXPORT). The
    // hypothesis types reference the arguments' FreeVariables, which
    // the field pass below re-binds along with every other occurrence.
    for (int j = (int)nonParamArgs.size() - 1; j >= 0; --j) {
        const auto& argument = nonParamArgs[j];
        if (!argument.isRecursive) continue;
        auto hypothesisType = makeInternalFreeVariable(motivePlaceholder);
        for (const auto& idx : argument.indicesForRecursiveCall) {
            hypothesisType = makeApplication(hypothesisType, idx);
        }
        hypothesisType = makeApplication(
            hypothesisType,
            makeInternalFreeVariable(argument.freshName));
        body = makePi("hypothesis_" + argument.displayHint,
                      hypothesisType, body);
    }
    for (int j = (int)nonParamArgs.size() - 1; j >= 0; --j) {
        const auto& argument = nonParamArgs[j];
        body = closeBinder(body, argument.freshName,
                           FreeVariableOrigin::Internal);
        body = makePi(argument.displayHint, argument.type, body);
    }

    return body;
}

// Builds the full type of the recursor for an inductive declaration that
// may have parameters and indices.
ExpressionPointer buildRecursorType(
    const std::string& inductiveName,
    const std::vector<std::string>& inductiveUniverseParameters,
    LevelPointer motiveLevel,
    ExpressionPointer kind,
    int numParameters,
    const std::vector<ConstructorSpec>& constructors) {
    const std::string motivePlaceholder = "motive";
    const std::string targetPlaceholder = "target";

    std::vector<LevelPointer> inductiveUniverseArgs;
    for (const auto& name : inductiveUniverseParameters) {
        inductiveUniverseArgs.push_back(makeLevelParam(name));
    }

    auto split = splitInductiveKind(kind, numParameters);

    // Build "T applied to all params and all indices" as a helper.
    auto buildInductiveApplied = [&]() {
        auto result =
            makeConstant(inductiveName, inductiveUniverseArgs);
        for (const auto& binder : split.binders) {
            result = makeApplication(
                result, makeInternalFreeVariable(binder.freshName));
        }
        return result;
    };

    // Build the motive's type:
    //   Π(i_1) ... Π(i_m). Π(_ : T params indices). Sort motiveLevel
    auto motiveType = makeSort(motiveLevel);
    motiveType = makePi("_", buildInductiveApplied(), motiveType);
    for (int i = (int)split.binders.size() - 1; i >= 0; --i) {
        if (split.binders[i].isParameter) continue;
        const auto& b = split.binders[i];
        motiveType = closeBinder(motiveType, b.freshName,
                                  FreeVariableOrigin::Internal);
        motiveType = makePi(b.displayHint, b.type, motiveType);
    }

    // Build case types for each constructor.
    std::vector<ExpressionPointer> caseTypes;
    caseTypes.reserve(constructors.size());
    for (const auto& constructor : constructors) {
        caseTypes.push_back(buildCaseType(
            inductiveName, inductiveUniverseArgs, split.binders,
            numParameters, motivePlaceholder, constructor));
    }

    // Innermost body: motive indices target.
    auto body = makeInternalFreeVariable(motivePlaceholder);
    for (const auto& b : split.binders) {
        if (!b.isParameter) {
            body = makeApplication(
                body, makeInternalFreeVariable(b.freshName));
        }
    }
    body = makeApplication(
        body, makeInternalFreeVariable(targetPlaceholder));

    // Wrap with target Pi.
    auto recursorType = closeBinder(body, targetPlaceholder,
                                     FreeVariableOrigin::Internal);
    recursorType = makePi("target", buildInductiveApplied(), recursorType);

    // Wrap with index Pis (innermost = last index).
    for (int i = (int)split.binders.size() - 1; i >= 0; --i) {
        if (split.binders[i].isParameter) continue;
        const auto& b = split.binders[i];
        recursorType = closeBinder(recursorType, b.freshName,
                                    FreeVariableOrigin::Internal);
        recursorType = makePi(b.displayHint, b.type, recursorType);
    }

    // Wrap with case Pis (innermost = last case). Cases aren't referenced
    // elsewhere in the type, so no name to close.
    for (int i = (int)constructors.size() - 1; i >= 0; --i) {
        recursorType = makePi("case_" + constructors[i].name,
                              caseTypes[i], recursorType);
    }

    // Wrap with motive Pi.
    recursorType = closeBinder(recursorType, motivePlaceholder,
                                FreeVariableOrigin::Internal);
    recursorType = makePi("motive", motiveType, recursorType);

    // Wrap with parameter Pis (innermost = last parameter).
    for (int i = (int)split.binders.size() - 1; i >= 0; --i) {
        if (!split.binders[i].isParameter) continue;
        const auto& b = split.binders[i];
        recursorType = closeBinder(recursorType, b.freshName,
                                    FreeVariableOrigin::Internal);
        recursorType = makePi(b.displayHint, b.type, recursorType);
    }

    return recursorType;
}

} // namespace

void addInductive(Environment& environment, std::string inductiveName,
                  std::vector<std::string> universeParameters,
                  ExpressionPointer kind,
                  int numParameters,
                  std::vector<ConstructorSpec> constructors) {
    validateName(inductiveName, "addInductive: inductive name");
    for (const auto& parameterName : universeParameters) {
        validateName(parameterName, "addInductive: universe parameter name");
    }
    for (const auto& constructor : constructors) {
        validateName(constructor.name, "addInductive: constructor name");
    }
    if (environment.declarations.count(inductiveName)) {
        throw TypeError("addInductive: name already declared: " + inductiveName);
    }
    KernelInstrumentationScope instrumentationScope("inductive " + inductiveName);
    // The kind must itself be a well-formed type. Walk the Pi-chain to
    // count Pis and find the terminal Sort.
    auto kindOfKind = weakHeadNormalForm(
        environment, inferType(environment, {}, kind));
    if (!std::holds_alternative<Sort>(kindOfKind->node)) {
        throw TypeError("addInductive: kind is not a type: " + inductiveName);
    }
    int totalPiCount = 0;
    auto kindWalker = kind;
    while (auto* pi = std::get_if<Pi>(&kindWalker->node)) {
        kindWalker = pi->codomain;
        totalPiCount++;
    }
    if (!std::holds_alternative<Sort>(kindWalker->node)) {
        throw TypeError(
            "addInductive: kind must end in a Sort: " + inductiveName);
    }
    if (numParameters < 0 || numParameters > totalPiCount) {
        throw TypeError(
            "addInductive: numParameters out of range for kind: " + inductiveName);
    }
    int numIndices = totalPiCount - numParameters;

    // Pre-register the inductive so that constructor types can reference it.
    std::vector<std::string> constructorNames;
    constructorNames.reserve(constructors.size());
    for (const auto& constructor : constructors) {
        constructorNames.push_back(constructor.name);
    }
    environment.declarations.emplace(
        inductiveName,
        Inductive{universeParameters, kind, constructorNames, numParameters});

    // A small lambda that rolls back partial registration on error.
    auto rollback = [&]() {
        environment.declarations.erase(inductiveName);
        for (const auto& constructor : constructors) {
            environment.declarations.erase(constructor.name);
        }
        environment.declarations.erase(inductiveName + "_recursor");
    };

    // Type-check and register each constructor. Each constructor type
    // must (a) itself be a well-formed type, (b) have only strictly-
    // positive occurrences of the inductive being declared, and (c) end
    // in the inductive (its conclusion is a Constant referring to it).
    for (int i = 0; i < (int)constructors.size(); ++i) {
        const auto& constructor = constructors[i];
        if (environment.declarations.count(constructor.name)) {
            rollback();
            throw TypeError(
                "addInductive: constructor name already taken: " + constructor.name);
        }
        try {
            auto kindOfConstructorType = weakHeadNormalForm(
                environment, inferType(environment, {}, constructor.type));
            if (!std::holds_alternative<Sort>(kindOfConstructorType->node)) {
                rollback();
                throw TypeError(
                    "addInductive: constructor type is not a type: " +
                    constructor.name);
            }
            auto conclusion =
                checkConstructorStrictlyPositive(inductiveName, constructor);
            // The conclusion may be `T params indices` (an Application chain
            // ending in the inductive's Constant). Peel the chain.
            auto conclusionHead = conclusion;
            while (auto* application =
                       std::get_if<Application>(&conclusionHead->node)) {
                conclusionHead = application->function;
            }
            if (auto* c = std::get_if<Constant>(&conclusionHead->node);
                !c || c->name != inductiveName) {
                rollback();
                throw TypeError(
                    "addInductive: constructor " + constructor.name +
                    " does not end in " + inductiveName);
            }
        } catch (const TypeError&) {
            rollback();
            throw;
        }
        environment.declarations.emplace(
            constructor.name,
            Constructor{universeParameters, inductiveName, i, constructor.type});
    }

    // Generate and register the recursor. For inductives that live in
    // Type, the motive's codomain is a fresh universe parameter — the
    // recursor is universe-polymorphic in the motive. For inductives that
    // live in Proposition, we restrict elimination: the motive's codomain is
    // forced to Proposition, so a proof can only eliminate to another proof
    // (preserving proof irrelevance). The empty Proposition inductive (zero
    // constructors, like False) is a singleton case where large elimination
    // is sound: there's no proof to extract data from in the first place.
    std::string recursorName = inductiveName + "_recursor";
    if (environment.declarations.count(recursorName)) {
        rollback();
        throw TypeError(
            "addInductive: recursor name already taken: " + recursorName);
    }
    bool inductiveLivesInProposition = false;
    {
        auto terminal = kind;
        while (auto* pi = std::get_if<Pi>(&terminal->node)) {
            terminal = pi->codomain;
        }
        if (auto* sort = std::get_if<Sort>(&terminal->node)) {
            auto level = levelAsConstant(sort->level);
            if (level && *level == 0) {
                inductiveLivesInProposition = true;
            }
        }
    }
    // Large elimination from Proposition is sound when there's nothing to extract:
    //   - empty inductives (zero constructors): no proof to extract from,
    //   - subsingleton inductives (exactly one constructor, each of whose
    //     non-parameter fields either is itself a proof — its type lives in
    //     Proposition — or appears among the indices of the constructor's
    //     conclusion): eliminating reveals nothing beyond what proof
    //     irrelevance and the index values already determine. This is
    //     Lean's criterion (type_checker book ch. 8), adopted verbatim so
    //     an external checker re-deriving our recursors from the inductive
    //     spec derives the same universe signature. Equality/And/Iff/Accessible
    //     large-eliminate; Exists does not (its witness field is data that
    //     appears in no index), exactly as in Lean.
    bool isSubsingleton = false;
    if (inductiveLivesInProposition && constructors.size() == 1) {
        try {
            isSubsingleton = true;
            Context fieldContext;
            std::vector<std::string> fieldsThatMustBeIndices;
            auto walker = constructors[0].type;
            int piIndex = 0;
            while (auto* pi = std::get_if<Pi>(&walker->node)) {
                std::string freshName =
                    "subsingletonField_" + std::to_string(piIndex);
                if (piIndex >= numParameters) {
                    auto fieldKind = weakHeadNormalForm(
                        environment,
                        inferType(environment, fieldContext, pi->domain));
                    auto* fieldSort = std::get_if<Sort>(&fieldKind->node);
                    auto fieldLevel =
                        fieldSort ? levelAsConstant(fieldSort->level)
                                  : std::nullopt;
                    bool fieldIsProof = fieldLevel && *fieldLevel == 0;
                    if (!fieldIsProof) {
                        fieldsThatMustBeIndices.push_back(freshName);
                    }
                }
                fieldContext.push_back(
                    {freshName, pi->domain, FreeVariableOrigin::Internal});
                walker = openBinder(pi->codomain, freshName,
                                    FreeVariableOrigin::Internal);
                piIndex++;
            }
            // The walker is now the conclusion `T params indices`. A field
            // "appears among the indices" when it is literally one of the
            // conclusion's index arguments.
            std::vector<ExpressionPointer> conclusionArgs;
            auto conclusionHead = walker;
            while (auto* application =
                       std::get_if<Application>(&conclusionHead->node)) {
                conclusionArgs.push_back(application->argument);
                conclusionHead = application->function;
            }
            std::reverse(conclusionArgs.begin(), conclusionArgs.end());
            for (const auto& fieldName : fieldsThatMustBeIndices) {
                bool appearsAsIndex = false;
                for (std::size_t i = numParameters;
                     i < conclusionArgs.size(); ++i) {
                    auto* freeVariable =
                        std::get_if<FreeVariable>(&conclusionArgs[i]->node);
                    if (freeVariable &&
                        freeVariable->origin == FreeVariableOrigin::Internal &&
                        freeVariable->name == fieldName) {
                        appearsAsIndex = true;
                        break;
                    }
                }
                if (!appearsAsIndex) {
                    isSubsingleton = false;
                    break;
                }
            }
        } catch (const TypeError&) {
            rollback();
            throw;
        }
    }
    bool allowLargeElimination =
        !inductiveLivesInProposition || constructors.empty() || isSubsingleton;

    LevelPointer motiveLevel;
    std::string motiveLevelName;  // empty if motive level is fixed at Proposition.
    if (allowLargeElimination) {
        motiveLevelName = "motiveLevel";
        auto inUse = [&](const std::string& candidate) {
            for (const auto& p : universeParameters) {
                if (p == candidate) return true;
            }
            return false;
        };
        for (int suffix = 1; inUse(motiveLevelName); ++suffix) {
            motiveLevelName = "motiveLevel_" + std::to_string(suffix);
        }
        motiveLevel = makeLevelParam(motiveLevelName);
    } else {
        motiveLevel = makeLevelConst(0);  // Proposition motive only.
    }
    auto recursorType = buildRecursorType(
        inductiveName, universeParameters, motiveLevel, kind, numParameters,
        constructors);
    try {
        auto kindOfRecursorType = weakHeadNormalForm(
            environment, inferType(environment, {}, recursorType));
        if (!std::holds_alternative<Sort>(kindOfRecursorType->node)) {
            rollback();
            throw TypeError(
                "internal: generated recursor type is ill-formed: " + recursorName);
        }
    } catch (const TypeError&) {
        rollback();
        throw;
    }
    std::vector<std::string> recursorUniverseParameters = universeParameters;
    if (!motiveLevelName.empty()) {
        recursorUniverseParameters.push_back(motiveLevelName);
    }
    environment.declarations.emplace(
        recursorName,
        Recursor{std::move(recursorUniverseParameters), inductiveName,
                 recursorType, (int)constructors.size(),
                 numParameters, numIndices});
}

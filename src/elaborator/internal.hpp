#pragma once

// Internal declaration of the Elaborator class.
//
// The elaborator is one large class (`class Elaborator`) whose method
// definitions are split across several translation units
// (elaborator.cpp + elaborator_*.cpp) to keep any single file tractable.
// This header holds the class DECLARATION so every such .cpp can define
// its slice of the methods out-of-line as `Elaborator::method(...)`.
//
// Methods that are still small / cross-cutting remain defined inline here;
// larger topical clusters are progressively moved into their own .cpp.
//
// NOT in an anonymous namespace: the class needs external linkage so its
// methods can be defined in different .cpp files and linked together.

#include "elaborator/elaborator.hpp"
#include "elaborator/term_utilities.hpp"  // LocalBinder + pure term helpers
#include "elaborator/lemma_search.hpp"
#include "kernel/printer.hpp"
#include "kernel/subtree_hash.hpp"

#include <chrono>
#include <cstdlib>
#include <iostream>
#include <sys/resource.h>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>



// Spine-head hash used to bucket rewrite lemmas in the calc auto-prover's
// lemma index (Phase 3). We walk the Application spine to its head and
// hash just that head's identifying tag (Constant name, or a leaf-shape
// tag for anything else). Two terms whose spines share the same head
// land in the same bucket — e.g. `(a+b)+c`, `a+b`, and `a+0` all bucket
// under `Natural.add` along with every other lemma whose LHS is rooted
// at that operator. The subsequent first-order matcher resolves the
// (small) bucket, and the kernel rechecks whatever proof term we emit.
//
// Coarse on purpose: argument shape can't be part of the bucket key
// because lemma binders match arbitrary subtrees, and the hash of a
// `BoundVariable` placeholder can't agree with the hash of an
// arbitrary concrete subterm at the same slot. Discrimination trees
// solve this by branching at wildcard slots; head-only buckets get
// most of the speedup at a fraction of the implementation cost.
inline uint64_t spineHash(ExpressionPointer expression) {
    constexpr uint64_t kTagWildcard = 0xfeULL;
    ExpressionPointer head = expression;
    while (auto* application =
               std::get_if<Application>(&head->node)) {
        head = application->function;
    }
    uint64_t h = subtree_hash::kSeed;
    if (auto* constant = std::get_if<Constant>(&head->node)) {
        h = subtree_hash::mix(h, subtree_hash::kTagConstant);
        h = subtree_hash::mix(h,
            subtree_hash::hashString(constant->name));
        return h;
    }
    if (std::holds_alternative<Pi>(head->node)) {
        return subtree_hash::mix(h, subtree_hash::kTagPi);
    }
    if (std::holds_alternative<Lambda>(head->node)) {
        return subtree_hash::mix(h, subtree_hash::kTagLambda);
    }
    if (std::holds_alternative<Let>(head->node)) {
        return subtree_hash::mix(h, subtree_hash::kTagLet);
    }
    // BoundVariable / FreeVariable / Sort heads share one wildcard
    // bucket: it's only consulted when the diff position itself is a
    // bare leaf (rare), which is also exactly when reverse-direction
    // identity lemmas need to fire.
    return subtree_hash::mix(h, kTagWildcard);
}

class Elaborator {
public:
    Elaborator(Environment& environment,
               std::vector<std::string>& importedModules)
        : environment_(environment),
          importedModules_(importedModules) {
        const char* tacticFlag = std::getenv("MATH_TIME_TACTICS");
        tacticTimingEnabled_ = tacticFlag && tacticFlag[0] != '\0'
            && tacticFlag[0] != '0';
        const char* autoProveProfileFlag =
            std::getenv("MATH_PROFILE_AUTOPROVER");
        autoProveProfileEnabled_ = autoProveProfileFlag
            && autoProveProfileFlag[0] != '\0'
            && autoProveProfileFlag[0] != '0';
        // Stage-1 ("statements-only") mode: elaborate each theorem's
        // statement (type) but skip its proof body, registering a
        // placeholder. Produces a module's interface without paying for its
        // proofs — the first pass of two-stage verification. Gated on an env
        // var so no call-site signatures change.
        const char* statementsOnlyFlag = std::getenv("MATH_STATEMENTS_ONLY");
        statementsOnly_ = statementsOnlyFlag
            && statementsOnlyFlag[0] != '\0'
            && statementsOnlyFlag[0] != '0';
    }

    ~Elaborator() {
        if (autoProveProfileEnabled_) emitAutoProverProfile();
        if (!tacticTimingEnabled_ || tacticStats_.empty()) return;
        // Dump in descending order of total time.
        std::vector<std::pair<std::string, TacticStats>> rows(
            tacticStats_.begin(), tacticStats_.end());
        std::sort(rows.begin(), rows.end(),
            [](const auto& a, const auto& b) {
                return a.second.totalMicros > b.second.totalMicros;
            });
        long long grandTotalMicros = 0;
        for (const auto& r : rows) grandTotalMicros += r.second.totalMicros;
        std::cerr << "[tactic] " << moduleName_
                  << " — strategy timings (grand total "
                  << (grandTotalMicros / 1000) << " ms):\n";
        for (const auto& r : rows) {
            double pct = grandTotalMicros > 0
                ? 100.0 * r.second.totalMicros / grandTotalMicros : 0.0;
            double avgUs = r.second.invocations > 0
                ? (double)r.second.totalMicros / r.second.invocations : 0.0;
            std::cerr << "  " << r.first
                      << ": inv=" << r.second.invocations
                      << " ok=" << r.second.successes
                      << " total=" << (r.second.totalMicros / 1000) << " ms"
                      << " (" << (int)pct << "%)"
                      << " avg=" << (int)avgUs << " us\n";
        }
    }

    // Dump the AutoProveRows collected under MATH_PROFILE_AUTOPROVER.
    // Emits two blocks on stderr:
    //   1. Per-row TSV — one line per outermost autoProveClaim call,
    //      columns documented at the top.
    //   2. Aggregates — per-tactic hit-rate vs. order; per-source
    //      distribution for contextFactMatch wins; local-binder-depth
    //      histogram; top library lemmas.
    void emitAutoProverProfile() {
        if (autoProveRows_.empty()) return;
        // Headline: time spent on losing tactic attempts vs the
        // winning one. Answers "how much would an oracle save?" —
        // the losing figure is the theoretical upper bound on the
        // savings from a (context, goal) → winning-tactic cache.
        //
        // NOTE: under profiling we keep running every tactic even
        // after one wins (to capture independent hit rates), but
        // normal operation short-circuits at the first success. So
        // "losing" here means failed attempts that ran BEFORE the
        // winner — those are the real waste. Attempts AFTER the
        // winner are profiling-only artefacts and excluded.
        long long losingUs = 0;
        long long winningUs = 0;
        long long claimsWithWinner = 0;
        long long claimsWithoutWinner = 0;
        for (const AutoProveRow& row : autoProveRows_) {
            bool hasWinner = !row.winningTactic.empty();
            if (hasWinner) ++claimsWithWinner;
            else ++claimsWithoutWinner;
            if (!hasWinner) {
                // Every attempt was a real loser (claim unresolved).
                for (const AutoProveAttempt& attempt : row.attempts) {
                    losingUs += attempt.micros;
                }
                continue;
            }
            for (const AutoProveAttempt& attempt : row.attempts) {
                if (attempt.tacticName == row.winningTactic
                    && attempt.succeeded) {
                    winningUs += attempt.micros;
                    break;  // stop at the winner — rest are artefacts
                }
                losingUs += attempt.micros;
            }
        }
        long long totalUs = losingUs + winningUs;
        double losingPct = totalUs > 0
            ? 100.0 * losingUs / totalUs : 0.0;
        std::cerr << "[autoprove-summary] " << moduleName_
                  << " claims=" << (claimsWithWinner + claimsWithoutWinner)
                  << " (closed=" << claimsWithWinner
                  << ", unresolved=" << claimsWithoutWinner << ")"
                  << " losing=" << (losingUs / 1000) << "ms"
                  << " winning=" << (winningUs / 1000) << "ms"
                  << " total=" << (totalUs / 1000) << "ms"
                  << " losing_share=" << (int)losingPct << "%"
                  << " (oracle could skip the losing share)\n";
        std::cerr << "[autoprove] " << moduleName_
                  << " — per-claim rows (TSV: "
                  << "file:line\tgoal_head\tgoal_size\twinner\t"
                  << "tactic\tok\tus\twin_source\tcand)\n";
        for (const AutoProveRow& row : autoProveRows_) {
            for (const AutoProveAttempt& attempt : row.attempts) {
                std::cerr << "[autoprove-row]\t"
                          << row.moduleName << ":" << row.line << "\t"
                          << row.goalHead << "\t"
                          << row.goalSize << "\t"
                          << row.winningTactic << "\t"
                          << attempt.tacticName << "\t"
                          << (attempt.succeeded ? "1" : "0") << "\t"
                          << attempt.micros << "\t"
                          << attempt.winner << "\t"
                          << attempt.candidatesTried
                          << "\n";
            }
        }
        // Aggregate: per-tactic independent hit-rates and timings.
        // These are decoupled from ordering — each tactic was tried
        // on every outermost claim site regardless of earlier wins.
        struct TacticAgg {
            long long inv = 0;
            long long ok = 0;
            long long totalUs = 0;
            long long winTotalUs = 0;
            long long winCount = 0;  // chosen as overall winner
        };
        std::unordered_map<std::string, TacticAgg> perTactic;
        std::unordered_map<std::string, long long> winnerSourceCounts;
        std::unordered_map<std::string, long long> winnerLibraryCounts;
        // Local-binder-depth histogram: distance from end (the most
        // recent binder is depth 0). For "library X" winners we
        // bucket under "library" overall and break out top names.
        std::unordered_map<int, long long> localDepthHistogram;
        for (const AutoProveRow& row : autoProveRows_) {
            for (const AutoProveAttempt& attempt : row.attempts) {
                auto& agg = perTactic[attempt.tacticName];
                ++agg.inv;
                agg.totalUs += attempt.micros;
                if (attempt.succeeded) ++agg.ok;
                if (attempt.tacticName == row.winningTactic) {
                    agg.winTotalUs += attempt.micros;
                    ++agg.winCount;
                    if (attempt.tacticName == "contextFactMatch"
                        && !attempt.winner.empty()) {
                        // attempt.winner is e.g.
                        //  "local binder kEqualsPredecessor"
                        //  "library Natural.le_through_max_left"
                        if (attempt.winner.rfind("local binder ", 0) == 0) {
                            ++winnerSourceCounts["local"];
                            // Depth from end isn't recorded yet — for now
                            // bucket as "local"; depth tracking is a
                            // straightforward follow-on (collectContextFacts
                            // walks N-1..0; we'd record the index).
                        } else if (attempt.winner.rfind("library ", 0) == 0) {
                            ++winnerSourceCounts["library"];
                            std::string lemmaName =
                                attempt.winner.substr(strlen("library "));
                            ++winnerLibraryCounts[lemmaName];
                        } else {
                            ++winnerSourceCounts["other"];
                        }
                    }
                }
            }
        }
        (void)localDepthHistogram;
        std::vector<std::pair<std::string, TacticAgg>> tacticRows(
            perTactic.begin(), perTactic.end());
        std::sort(tacticRows.begin(), tacticRows.end(),
            [](const auto& a, const auto& b) {
                return a.second.totalUs > b.second.totalUs;
            });
        std::cerr << "[autoprove] aggregate — per-tactic"
                  << " (tactic / inv / ok / hit_rate / "
                  << "avg_us / total_ms / wins / win_avg_us)\n";
        for (const auto& r : tacticRows) {
            double rate = r.second.inv > 0
                ? 100.0 * r.second.ok / r.second.inv : 0.0;
            double avgUs = r.second.inv > 0
                ? (double)r.second.totalUs / r.second.inv : 0.0;
            double winAvgUs = r.second.winCount > 0
                ? (double)r.second.winTotalUs / r.second.winCount : 0.0;
            std::cerr << "  " << r.first
                      << ": inv=" << r.second.inv
                      << " ok=" << r.second.ok
                      << " rate=" << (int)rate << "%"
                      << " avg=" << (int)avgUs << " us"
                      << " total=" << (r.second.totalUs / 1000) << " ms"
                      << " wins=" << r.second.winCount
                      << " win_avg=" << (int)winAvgUs << " us\n";
        }
        // Source-category breakdown for contextFactMatch.
        if (!winnerSourceCounts.empty()) {
            std::cerr << "[autoprove] aggregate — contextFactMatch"
                      << " winner source (local vs library)\n";
            for (const auto& kv : winnerSourceCounts) {
                std::cerr << "  " << kv.first << ": " << kv.second << "\n";
            }
        }
        if (!winnerLibraryCounts.empty()) {
            std::vector<std::pair<std::string, long long>> libRows(
                winnerLibraryCounts.begin(), winnerLibraryCounts.end());
            std::sort(libRows.begin(), libRows.end(),
                [](const auto& a, const auto& b) {
                    return a.second > b.second;
                });
            std::cerr << "[autoprove] aggregate — top library "
                      << "lemmas chosen by contextFactMatch\n";
            int count = 0;
            for (const auto& r : libRows) {
                std::cerr << "  " << r.second << "\t" << r.first << "\n";
                if (++count >= 20) break;
            }
        }
    }

    // Run a strategy and track its timing + success rate. The
    // strategy must return ExpressionPointer (nullptr on miss). When
    // MATH_TIME_TACTICS isn't set, this is a no-op wrapper.
    // Count expression-tree nodes (Constants, BVs, FVs, Applications,
    // Pis, Lambdas, Lets, Sorts). Used by the diagnostic probes below
    // — a structurally-large term suggests pathological substitution
    // / unfolding behaviour worth investigating.

    template <typename F>
    ExpressionPointer runTactic(const std::string& name, F&& fn) {
        if (!tacticTimingEnabled_) return fn();
        ++tacticStats_[name].invocations;
        auto t0 = std::chrono::steady_clock::now();
        ExpressionPointer result = fn();
        auto t1 = std::chrono::steady_clock::now();
        tacticStats_[name].totalMicros +=
            std::chrono::duration_cast<std::chrono::microseconds>(
                t1 - t0).count();
        if (result) ++tacticStats_[name].successes;
        return result;
    }

    // RAII helper to time a scope (e.g. an elaborator function) and
    // attribute the total to a named bucket in `tacticStats_`. Counts
    // each entry as an invocation; doesn't track success/failure (the
    // function may throw or do anything). No-op when timing isn't on.
    struct TimedScope {
        Elaborator& self_;
        const std::string name_;
        std::chrono::steady_clock::time_point t0_;
        bool active_;
        TimedScope(Elaborator& self, const char* name)
            : self_(self), name_(name), active_(self.tacticTimingEnabled_) {
            if (active_) {
                ++self_.tacticStats_[name_].invocations;
                t0_ = std::chrono::steady_clock::now();
            }
        }
        ~TimedScope() {
            if (!active_) return;
            auto t1 = std::chrono::steady_clock::now();
            self_.tacticStats_[name_].totalMicros +=
                std::chrono::duration_cast<std::chrono::microseconds>(
                    t1 - t0_).count();
        }
    };

    // When true, every `by <proof>` annotation on a calc step is
    // also tried with the auto-prover; if the auto-prover closes the
    // step on its own, a warning fires. Drives the
    // `--check-redundant-by` CLI flag.
    void setReportRedundantBy(bool flag) { reportRedundantBy_ = flag; }

    // Injects the lazy whole-library snapshot used to enrich failing-proof
    // errors with unimported-lemma suggestions. See elaborateModule.
    void setLibrarySearchProvider(
        std::function<const LibrarySearchIndex*()> provider) {
        librarySearchProvider_ = std::move(provider);
    }

    // When true, the redundant-by check also fires on non-equality
    // calc steps (≤/</≥/>). Off by default because for large files
    // it can be expensive (the per-step lemma-index lookup iterates
    // all environment declarations). Drives the
    // `--check-redundant-by-non-eq` CLI flag.
    void setReportRedundantByNonEq(bool flag) {
        reportRedundantByNonEq_ = flag;
    }

    // When true, after elaborating a calc chain, check each internal
    // step's endpoint to see whether the auto-prover could close the
    // combined step (prev-prev → next) without going through it. If
    // yes, emit a warning so the user can remove the redundant
    // intermediate. Off by default — the per-step auto-prover
    // attempts are expensive on long chains. Drives the
    // `--check-redundant-calc-steps` CLI flag.
    void setReportRedundantCalcSteps(bool flag) {
        reportRedundantCalcSteps_ = flag;
    }

    void runModule(const SurfaceModule& module) {
        moduleName_ = module.moduleName;
        // Seed the rewrite-lemma index from theorems loaded via .mathv
        // dependencies. New theorems added during this module's
        // elaboration get registered incrementally in
        // elaborateDefinition / elaboratePatternMatchDefinition.
        seedAlgebraicRegistryFromEnvironment();
        // Opt-in: enable the kernel's structural-hash WHNF cache for
        // the duration of this module. Big win on files where the
        // elaborator hands the kernel many freshly-allocated but
        // structurally-identical subexpressions (Real/supremum.math
        // is the canonical example).
        const char* cacheFlag = std::getenv("MATH_KERNEL_CACHE");
        bool enableKernelCache = cacheFlag && cacheFlag[0] != '\0'
            && cacheFlag[0] != '0';
        bool previousKernelCache = kernelCacheEnabled;
        if (enableKernelCache) kernelCacheEnabled = true;
        const char* hcFlag = std::getenv("MATH_HASH_CONS");
        bool enableHashCons = hcFlag && hcFlag[0] != '\0'
            && hcFlag[0] != '0';
        bool previousHashCons = g_hashConsEnabled;
        if (enableHashCons) g_hashConsEnabled = true;
        const char* kpFlag = std::getenv("MATH_KERNEL_PROFILE");
        bool enableKernelProfile = kpFlag && kpFlag[0] != '\0'
            && kpFlag[0] != '0';
        bool previousKernelProfile = kernelProfileEnabled;
        if (enableKernelProfile) kernelProfileEnabled = true;
        const char* timeFlag = std::getenv("MATH_TIME_DECLARATIONS");
        bool timeDeclarations = timeFlag && timeFlag[0] != '\0'
            && timeFlag[0] != '0';
        for (const auto& statement : module.statements) {
            if (timeDeclarations) {
                auto t0 = std::chrono::steady_clock::now();
                elaborateTopStatement(statement);
                auto t1 = std::chrono::steady_clock::now();
                long long elapsedMs =
                    std::chrono::duration_cast<std::chrono::milliseconds>(
                        t1 - t0).count();
                // Emit only non-trivial timings to keep noise low.
                if (elapsedMs >= 50) {
                    std::string label = topStatementLabel(statement);
                    std::cerr << "[time] " << moduleName_
                              << " " << label
                              << ": " << elapsedMs << " ms\n";
                }
            } else {
                elaborateTopStatement(statement);
            }
        }
        if (enableKernelCache) kernelCacheEnabled = previousKernelCache;
        if (enableKernelProfile) kernelProfileEnabled = previousKernelProfile;
        if (enableHashCons) g_hashConsEnabled = previousHashCons;
        if (timeDeclarations || tacticTimingEnabled_) {
            struct rusage ru;
            if (getrusage(RUSAGE_SELF, &ru) == 0) {
                // On macOS ru_maxrss is bytes; on Linux it's kilobytes.
                // Normalize to MB; on macOS this is bytes/1048576, on
                // Linux it's kbytes/1024 — same arithmetic.
#if defined(__APPLE__)
                long long mb = ru.ru_maxrss / (1024 * 1024);
#else
                long long mb = ru.ru_maxrss / 1024;
#endif
                std::cerr << "[memory] " << moduleName_
                          << " peak RSS=" << mb << " MB\n";
            }
        }
    }

    // Extract a short identifier from a top-level statement for
    // use in timing diagnostics. Falls back to "?" if the statement
    // kind doesn't have a name field.
    std::string topStatementLabel(
        const SurfaceTopStatement& statement) {
        if (auto* d = std::get_if<SurfaceDefinitionDeclaration>(&statement)) {
            return d->name;
        }
        if (auto* a = std::get_if<SurfaceAxiomDeclaration>(&statement)) {
            return a->name;
        }
        if (auto* i = std::get_if<SurfaceInductiveDeclaration>(&statement)) {
            return i->name;
        }
        if (auto* imp = std::get_if<SurfaceImportDeclaration>(&statement)) {
            return std::string("import ") + imp->moduleName;
        }
        return "?";
    }

    // Walk the pre-loaded environment and run shape detection on
    // every Definition's declared type. We restrict to Definitions
    // (not Axioms) since theorems serialise as Definitions with a
    // proof body.
    void seedAlgebraicRegistryFromEnvironment() {
        for (const auto& entry : environment_.declarations) {
            const std::string& name = entry.first;
            const auto& declaration = entry.second;
            if (auto* def = std::get_if<Definition>(&declaration)) {
                registerAlgebraicShape(name, def->type);
            }
        }
    }

    ExpressionPointer runExpression(const SurfaceExpression& expression) {
        return elaborateExpression(expression, {});
    }

private:
    // -------- diagnostic context stack --------
    //
    // The elaborator keeps a stack of "while doing X at line Y" frames
    // as it descends. Errors prepend the stack so the user sees a
    // breadcrumb trail from the surface position to the failure. The
    // Frame guard is RAII: construct to push, destruct to pop. Push
    // before any non-trivial elaboration step; the destructor will run
    // even on exception unwinding, so we don't need explicit pops.

    // Each context frame records what the elaborator was doing AND, when
    // the caller can supply them, the proof context (local binders) and
    // the goal (expected type) at the point the frame was pushed.
    // Errors dump both alongside the breadcrumb so the user sees both
    // "where" and "what was being proved" at every level of the stack.
    struct FrameSnapshot {
        std::string description;
        std::vector<LocalBinder> contextSnapshot;  // copy at push time
        ExpressionPointer expectedType;             // may be null
        int line = 0;                                // 0 = unknown
        int column = 0;                              // 0 = unknown
    };

    struct Frame {
        Elaborator& elaborator;
        Frame(Elaborator& target, std::string description)
            : elaborator(target) {
            elaborator.contextFrames_.push_back(
                FrameSnapshot{std::move(description), {}, nullptr,
                               0, 0});
        }
        Frame(Elaborator& target, std::string description,
              const std::vector<LocalBinder>& localBinders,
              ExpressionPointer expectedType)
            : elaborator(target) {
            elaborator.contextFrames_.push_back(
                FrameSnapshot{std::move(description),
                               localBinders, expectedType, 0, 0});
        }
        Frame(Elaborator& target, std::string description,
              const std::vector<LocalBinder>& localBinders,
              ExpressionPointer expectedType,
              int line, int column)
            : elaborator(target) {
            elaborator.contextFrames_.push_back(
                FrameSnapshot{std::move(description),
                               localBinders, expectedType,
                               line, column});
        }
        // Position-only frame (no context/goal snapshot) — for top-level
        // declarations that want their source line as the error anchor.
        Frame(Elaborator& target, std::string description,
              int line, int column)
            : elaborator(target) {
            elaborator.contextFrames_.push_back(
                FrameSnapshot{std::move(description), {}, nullptr,
                               line, column});
        }
        ~Frame() { elaborator.contextFrames_.pop_back(); }
        Frame(const Frame&) = delete;
        Frame& operator=(const Frame&) = delete;
    };

    // Recursively reduces beta-redexes in an expression for display.
    // Unlike `weakHeadNormalForm`, this does NOT unfold Definition
    // applications — those produce huge expanded forms in errors
    // ("Natural.multiply 3 4" stays as written rather than expanding
    // into the Natural_recursor chain). We only reduce
    // `App(Lambda(x, T, body), arg)` patterns at any depth.
    ExpressionPointer betaNormalizeForDisplay(
        ExpressionPointer expression) const {
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                betaNormalizeForDisplay(pi->domain),
                betaNormalizeForDisplay(pi->codomain));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                betaNormalizeForDisplay(lambda->domain),
                betaNormalizeForDisplay(lambda->body));
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            ExpressionPointer fn = betaNormalizeForDisplay(
                application->function);
            ExpressionPointer arg = betaNormalizeForDisplay(
                application->argument);
            if (auto* lambda = std::get_if<Lambda>(&fn->node)) {
                ExpressionPointer reduced = substitute(
                    lambda->body, 0, arg);
                return betaNormalizeForDisplay(reduced);
            }
            return makeApplication(fn, arg);
        }
        return expression;
    }

    std::string prettyPrintForDisplay(
        ExpressionPointer expression) const {
        std::string raw =
            prettyPrint(betaNormalizeForDisplay(expression));
        // The printer prefixes Internal-origin FreeVariables with '@'
        // so that any leak into user output is visible. In error
        // messages we deliberately open binders into named FreeVars,
        // so the `@` markers are noise; strip them.
        std::string stripped;
        stripped.reserve(raw.size());
        for (char character : raw) {
            if (character != '@') stripped.push_back(character);
        }
        return stripped;
    }

    // Pretty-print an expression that lives in a local-binder scope.
    // Opens each binder as a named FreeVariable so the printer shows
    // the user's name rather than a bare `<bound k>` index. `count`
    // optionally limits how many binders are visible (useful when
    // printing the type of binder `i`, which references only the
    // first `i` binders).
    std::string prettyPrintInLocalScope(
        ExpressionPointer expression,
        const std::vector<LocalBinder>& localBinders,
        size_t count) const {
        // Open with User-origin so the printer doesn't mark the
        // resulting FreeVariables with `@` (which is reserved for
        // signalling that an Internal-origin variable leaked).
        // Beta-normalise too so the printed form has no left-over
        // redexes (motive applications, etc.).
        ExpressionPointer opened = expression;
        for (size_t i = count; i > 0; --i) {
            opened = openBinder(opened, localBinders[i - 1].name,
                                 FreeVariableOrigin::User);
        }
        return prettyPrint(betaNormalizeForDisplay(opened));
    }
    std::string prettyPrintInLocalScope(
        ExpressionPointer expression,
        const std::vector<LocalBinder>& localBinders) const {
        return prettyPrintInLocalScope(expression, localBinders,
                                         localBinders.size());
    }

    // E1 surface #1: turn a failed auto-prove into a list of candidate
    // lemmas whose CONCLUSION matches the goal's shape (the same engine
    // behind `kernel search --goal`). Appended to the claim/`done`
    // failure message so the author — especially an LLM that would
    // otherwise guess a plausible-but-wrong name — sees the real lemma,
    // its signature, and the hypotheses still to discharge, exactly
    // where they are already looking. Best-effort: any exception (or an
    // empty result) yields no text, preserving the base error.
    std::string searchSuggestions(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        size_t limit = 5) const {
        try {
            ExpressionPointer goalOpened = goalClosed;
            for (size_t i = localBinders.size(); i > 0; --i) {
                goalOpened = openBinder(goalOpened,
                                        localBinders[i - 1].name,
                                        FreeVariableOrigin::User);
            }
            // Search the WHOLE library when a snapshot is available (the
            // verify-with-cache path), so a lemma that isn't imported yet
            // still surfaces — tagged with the import to add. Without the
            // snapshot (tests / legacy verify), search the in-scope
            // environment alone. A hit is "in scope" iff it is already a
            // declaration in environment_; otherwise we cite its module.
            const LibrarySearchIndex* index =
                librarySearchProvider_ ? librarySearchProvider_() : nullptr;
            static const std::set<std::string> noExclusions;
            const Environment& searchEnvironment =
                index ? index->environment : environment_;
            const std::set<std::string>& excluded =
                index ? index->excludedNames : noExclusions;
            std::string head;
            std::vector<LemmaSearchHit> hits = computeGoalHits(
                searchEnvironment, goalOpened, head, excluded);
            if (hits.empty()) return "";
            std::string out =
                "\n  search by conclusion shape — candidates "
                "(cite one as `by <lemma>(…)`):";
            size_t shown = std::min(limit, hits.size());
            for (size_t i = 0; i < shown; ++i) {
                out += "\n    " + hits[i].name + " : "
                     + hits[i].signature;
                if (!hits[i].needs.empty()) {
                    out += "   [needs: ";
                    for (size_t j = 0; j < hits[i].needs.size(); ++j) {
                        if (j) out += ", ";
                        out += prettyPrint(hits[i].needs[j]);
                    }
                    out += "]";
                }
                // Tag lemmas that are not yet in scope with the import.
                if (index && !environment_.lookup(hits[i].name)) {
                    auto moduleIterator =
                        index->nameToModule.find(hits[i].name);
                    if (moduleIterator != index->nameToModule.end()) {
                        out += "\n        (needs import "
                             + moduleIterator->second + ")";
                    }
                }
            }
            return out;
        } catch (...) {
            return "";
        }
    }

    // Tail for a "couldn't prove this step" error: the step goal
    // (LHS rel RHS) followed by library-lemma candidates keyed by the
    // goal's conclusion shape. The surrounding frame already dumps the
    // in-scope hypotheses; this adds the concrete goal and suggestions.
    // Guarded so pretty-printing never amplifies the primary error.
    std::string couldNotProveStepHint(
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        const std::string& relationSymbol,
        ExpressionPointer stepRelationType,
        const std::vector<LocalBinder>& localBinders) const {
        std::string goal;
        try {
            goal = "\n    goal: "
                 + prettyPrintInLocalScope(previousKernel, localBinders)
                 + " " + relationSymbol + " "
                 + prettyPrintInLocalScope(nextKernel, localBinders);
        } catch (...) { goal.clear(); }
        std::string hints;
        try {
            hints = searchSuggestions(stepRelationType, localBinders);
        } catch (...) { hints.clear(); }
        return goal + hints;
    }

    // ---- Term representation convention (read before touching the helpers
    //      that move terms between scopes) ----
    //
    // A term handled by the elaborator is in one of two representations
    // relative to the ambient `localBinders` (the in-scope hypotheses):
    //
    //  • CLOSED over local binders — each in-scope hypothesis appears as a
    //    `BoundVariable` (de Bruijn), so the term is closed: it references no
    //    free hypothesis directly. This is the *storage* form: what
    //    `elaborateExpression` / `autoProveClaim` return, what gets pushed on
    //    `LocalBinder`s, and what `goalClosed` / `hintType` hold. Invariant:
    //    such a term must satisfy `maxFreeBoundVariable < localBinders.size()`
    //    (its bound-variable refs all land within the local scope).
    //
    //  • OPENED over local binders — each hypothesis appears as a named
    //    `FreeVariable` valid in `buildContextFromLocalBinders(localBinders)`.
    //    This is the *kernel-operation* form: what `inferType`,
    //    `isDefinitionallyEqual`, and `weakHeadNormalForm` consume.
    //
    // Conversions: `openOverLocalBinders` (closed → opened),
    // `closeOverLocalBinders` (opened → closed). `inferTypeInLocalContext`
    // takes a CLOSED term, opens it, and returns an OPENED type.
    //
    // The trap: a helper that hands back a malformed term (a bound variable
    // escaping the local scope) passes silent until the next `inferType`,
    // which dies deep in the kernel with "bare BoundVariable reached
    // inferType". `assertClosedOverLocalBinders` turns that into an O(1)
    // check at the boundary, naming the producer.
    void assertClosedOverLocalBinders(
        const ExpressionPointer& term,
        const std::vector<LocalBinder>& localBinders,
        const char* where) const {
        int n = static_cast<int>(localBinders.size());
        if (term->maxFreeBoundVariable >= n) {
            throw TypeError(
                std::string("internal: ") + where
                + " produced a term that is not closed over its local binders"
                  " (maxFreeBoundVariable="
                + std::to_string(term->maxFreeBoundVariable)
                + ", local binders=" + std::to_string(n)
                + ") — a bound variable escapes the local scope");
        }
    }

    // Const version of openOverLocalBinders (the existing one in this
    // class is non-const because it shares the helper used during
    // mutating elaboration).

    std::string formatErrorWithContext(const std::string& message) const {
        if (contextFrames_.empty()) return message;
        std::string result;
        // Most-recent frame first (innermost work), then progressively
        // outer frames. Each frame on its own line indented under the
        // last so the breadcrumb reads top-to-bottom from outer cause
        // to inner failure. For frames carrying a context snapshot
        // and/or a goal, dump those one indent deeper.
        for (auto iterator = contextFrames_.rbegin();
             iterator != contextFrames_.rend(); ++iterator) {
            result += iterator->description;
            result += "\n";
            // Context dump (suppressed when the snapshot is empty —
            // top-level frames before any binder is pushed don't add
            // anything by saying "(no binders)").
            if (!iterator->contextSnapshot.empty()) {
                result += "    context:\n";
                for (size_t i = 0;
                     i < iterator->contextSnapshot.size(); ++i) {
                    const auto& binder = iterator->contextSnapshot[i];
                    // Type may reference earlier binders (de Bruijn);
                    // open those names so the printout reads as the
                    // user wrote them.
                    std::string printedType;
                    try {
                        printedType = prettyPrintInLocalScope(
                            binder.type, iterator->contextSnapshot, i);
                    } catch (...) {
                        // Pretty-printing must never amplify the
                        // primary error. Fall back to a marker.
                        printedType = "<un-printable>";
                    }
                    result += "      " + binder.name + " : "
                            + printedType + "\n";
                }
            }
            // Goal dump (only when supplied — most internal frames
            // don't have a meaningful local goal to report).
            if (iterator->expectedType) {
                std::string printedGoal;
                try {
                    printedGoal = prettyPrintInLocalScope(
                        iterator->expectedType,
                        iterator->contextSnapshot);
                } catch (...) {
                    printedGoal = "<un-printable>";
                }
                result += "    goal: " + printedGoal + "\n";
            }
            result += "  ";
        }
        result += message;
        return result;
    }

    [[noreturn]] void throwElaborate(const std::string& message) const {
        // Pick up the most recent (innermost) frame that has a known
        // source position; that's the best anchor for an editor to
        // highlight.
        int line = 0;
        int column = 0;
        for (auto iter = contextFrames_.rbegin();
             iter != contextFrames_.rend(); ++iter) {
            if (iter->line != 0) {
                line = iter->line;
                column = iter->column;
                break;
            }
        }
        throw ElaborateError(
            formatErrorWithContext(message), line, column);
    }

    // Wraps a kernel TypeError with the elaborator's context stack and
    // any pretty-printed types the kernel attached. Use in catch
    // blocks around kernel `inferType` / `isDefinitionallyEqual`
    // calls.
    [[noreturn]] void rethrowKernelError(const TypeError& error) const {
        // WS1 (PLAN_LESS_CIC_STYLE.md): this is the single chokepoint where
        // a kernel `TypeError` becomes user-facing. Ideally the elaborator
        // checks first and the kernel only confirms; where a gap remains,
        // we re-author the kernel's CIC-shaped wording here in surface
        // terms. The embedded type rendering is already math-shaped
        // (prettyPrintForDisplay), so only the message text and the
        // expected/actual labels need translating. A message we have NOT
        // taught a surface form keeps the literal "kernel: " prefix — that
        // prefix is the provenance tag the error-corpus audit keys on, so
        // leaving it on unmapped messages keeps new leaks visible.
        const std::string what = error.what();
        // Bucket A (WS8): an "internal:" error means the elaborator built a
        // malformed term and the kernel caught it (e.g. a bare BoundVariable
        // reaching inferType). This is a *defect*, never the user's fault,
        // and must never surface CIC vocabulary. Show a generic, math-free
        // "please report" message; log the raw detail to stderr for the
        // developer. No expected/actual types (they're internal noise).
        if (what.rfind("internal:", 0) == 0) {
            std::cerr << "internal diagnostic (please report): " << what
                      << "\n";
            auto [line, column] = innermostFramePosition();
            throw ElaborateError(formatErrorWithContext(
                "internal error: the elaborator built a malformed term here "
                "(this is a bug, not a problem with your proof — please "
                "report it)"),
                line, column);
        }
        std::string message;
        const char* expectedLabel = "expected type: ";
        const char* actualLabel = "actual type:   ";
        if (what == "Application: function is not of Pi type") {
            message = "this is being applied to an argument, but it is not "
                      "a function";
            actualLabel = "it has type:   ";
        } else if (what
                   == "Application: argument type does not match Pi domain") {
            message = "this argument has the wrong type for the function it "
                      "is given to";
            expectedLabel = "the function expects: ";
            actualLabel = "but this argument is: ";
        } else {
            message = "kernel: " + what;
        }
        if (error.expectedType) {
            message += "\n    ";
            message += expectedLabel;
            message += prettyPrintForDisplay(error.expectedType);
        }
        if (error.actualType) {
            message += "\n    ";
            message += actualLabel;
            message += prettyPrintForDisplay(error.actualType);
        }
        // Anchor the error at the innermost frame that knows its source
        // position (the calc step / argument / theorem currently being
        // elaborated). Without this a kernel TypeError reported `:1:1` with
        // only the theorem name, leaving the user to hunt for the line.
        auto [line, column] = innermostFramePosition();
        throw ElaborateError(formatErrorWithContext(message), line, column);
    }

    // The innermost context frame that carries a source position (the calc
    // step / argument / theorem currently being elaborated), or {0,0}.
    // Same walk throwElaborate uses to anchor kernel errors.
    std::pair<int, int> innermostFramePosition() const {
        for (auto iter = contextFrames_.rbegin();
             iter != contextFrames_.rend(); ++iter) {
            if (iter->line != 0) {
                return {iter->line, iter->column};
            }
        }
        return {0, 0};
    }

    // WS1 (PLAN_LESS_CIC_STYLE.md): make the elaborator authoritative at
    // the definition-finalization boundary. `addDefinition` (the kernel)
    // performs three checks — name-uniqueness, declared-type-is-a-type,
    // and body-type-matches-declared-type — and on failure throws a
    // CIC-shaped `TypeError` ("addDefinition: body type does not match
    // declared type", …). Were that the FIRST check, its wording would
    // reach the user. So we run the identical checks here first, on the
    // closed `declaredType`/`body` (empty context — `addDefinition` binds
    // no universe params either, see kernel.cpp), and report any failure
    // as mathematics. The kernel call immediately below then only ever
    // CONFIRMS. `noun` is "theorem"/"definition" for message phrasing;
    // `bodyNoun` is "proof"/"body".
    void checkDefinitionWellFormedOrThrow(
            const std::string& name,
            const ExpressionPointer& declaredType,
            const ExpressionPointer& body,
            const char* noun,
            const char* bodyNoun) {
        if (environment_.declarations.count(name)) {
            throwElaborate(std::string("a declaration named '") + name
                + "' already exists");
        }
        // The declared type must itself be a type (live in some `Sort`).
        ExpressionPointer declaredKind;
        try {
            declaredKind = weakHeadNormalForm(
                environment_, inferType(environment_, {}, declaredType));
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        if (!std::holds_alternative<Sort>(declaredKind->node)) {
            throwElaborate(std::string("the declared type of ") + noun + " '"
                + name + "' is not itself a type: `"
                + prettyPrintForDisplay(declaredType)
                + "` has type `" + prettyPrintForDisplay(declaredKind)
                + "`, which is not a proposition or a type");
        }
        // The body must have the declared type.
        ExpressionPointer inferredBodyType;
        try {
            inferredBodyType = inferType(environment_, {}, body);
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        if (!isDefinitionallyEqual(environment_, {}, inferredBodyType,
                                   declaredType)) {
            throwElaborate(std::string("the ") + bodyNoun + " of " + noun
                + " '" + name + "' does not have its declared type\n"
                "    declared type:        "
                + prettyPrintForDisplay(declaredType) + "\n"
                "    but this " + bodyNoun + " has type: "
                + prettyPrintForDisplay(inferredBodyType));
        }
    }

    // -------- top-level statements --------

    void elaborateTopStatement(const SurfaceTopStatement& statement);

    // `convention p [q ...] : T [with H1 [, H2 ...]];` registers each
    // name (`p`, `q`, …) as a key in `conventionRegistry_`. The stored
    // value is the convention's binder shape: the carrier type and the
    // list of side-condition expressions (each referencing the names).
    // When `elaborateDefinition` later sees a free use of `p` in a
    // declaration's signature, it prepends an implicit binder for `p`
    // and one implicit binder per side-condition.
    void elaborateConventionDeclaration(
        const SurfaceConventionDeclaration& declaration);

    // `instance <name>` — register `name` as the canonical instance for
    // its (structure, carrier) pair. v1 supports concrete-carrier,
    // non-parameterized instances (e.g. `Integer.add_is_group :
    // IsGroup(Integer, …)`). Reject-on-ambiguity: a second instance for
    // the same (structure, carrier) is refused, mirroring the coercion
    // registry — never guess, never backtrack.
    void elaborateInstanceDeclaration(
        const SurfaceInstanceDeclaration& declaration);

    // Validate and register an `operator (sym) on (T1, T2) := F`
    // declaration. The function `F` must exist in scope and have type
    // `T1 → T2 → R` for some result type `R`. `T1` and `T2` must each
    // be the head Constant of a known type (axiomatic or via inductive/
    // definition), or the wildcard `_` when the slot's type is generic
    // (e.g. the LHS of `∈ : T → Set(T) → Prop` for any carrier T).
    // When a side is `_`, the head check is skipped — at dispatch time,
    // the lookup falls back to `(sym, _, RightType)` / `(sym, LeftType,
    // _)` / `(sym, _, _)` if no exact match is found.
    void elaborateOperatorDeclaration(
        const SurfaceOperatorDeclaration& declaration);

    // Validate and register an `overload alias := F` declaration. The
    // function `F` must exist; the alias accumulates a list of fully-
    // qualified candidates that the elaborator picks among by argument-
    // type matching at call sites.
    void elaborateCongruenceDeclaration(
        const SurfaceCongruenceDeclaration& declaration);

    void elaborateOverloadDeclaration(
        const SurfaceOverloadDeclaration& declaration);

    // Validate and register a `coercion (S, T) := F` declaration.
    //
    // F must have type `S → T` (both head Constants). After validation
    // we add the direct edge and compute the transitive closure with
    // existing coercions; any registration whose closure step would
    // overwrite a different existing chain is rejected (diamond).
    void elaborateCoercionDeclaration(
        const SurfaceCoercionDeclaration& declaration);

    // Does `expressionType` have the given Constant name at its head?
    // Checks the *raw* head first (so a parameter declared as
    // `Rational` matches `Rational`, even though `Rational` δ-reduces
    // to `Quotient(...)`). Falls back to WHNF if the raw head isn't a
    // Constant. Used for validating operator-declaration signatures.
    bool typeHasHeadName(ExpressionPointer expressionType,
                           const std::string& expectedName);

    void elaborateAxiom(const SurfaceAxiomDeclaration& declaration);

    // Walk a surface type expression's leading Pi-binders and count
    // names across the consecutive prefix of implicit binders. Stops
    // at the first explicit binder, the first non-Pi node, or end of
    // chain. Used by `elaborateAxiom` to register implicit-argument
    // counts so call-site inference can fire.
    int countLeadingImplicitArgumentNamesInType(
        SurfaceExpressionPointer typeExpression);

    // Like `referencesBoundBelowThreshold` but allows the abstraction
    // index `abstractIndex` — any Bound var equal to that index (after
    // depth adjustment) is treated as the variable we plan to abstract
    // over and so isn't counted as a capture. Other Bound vars below
    // threshold ARE counted as captures and force the caller to give up.
    bool referencesOtherBoundsBelowThreshold(
        ExpressionPointer expression,
        int threshold,
        int abstractIndex,
        int currentDepth = 0);

    // Repeatedly abstracts over a sequence of BoundVariable indices.
    // `indices` is in outermost-to-innermost binder order — i.e.
    // indices[0] becomes the outer Lambda's binder and indices.back()
    // becomes the inner Lambda's binder. After each abstraction every
    // other outer reference shifts up by one, so the i-th abstraction
    // targets the original index shifted by i.

    // Rewrites `expression` so that BoundVariable(targetIndex) becomes
    // BoundVariable(0) at every depth, and every OTHER BoundVariable
    // that refers to outer scope is shifted up by one. Used to build
    // a motive that abstracts over a specific local-binder variable
    // (the scrutinee of a `cases` expression): the resulting term is
    // suitable as the body of a Lambda whose binder takes the
    // scrutinee's place at index 0.

    // Counts leading implicit binder names in a declaration's argument
    // list. Throws if `{x:T}` and `(y:U)` are interleaved (Phase 2.1
    // restricts implicit binders to a leading consecutive prefix). The
    // result is the total number of NAMES across the leading implicit
    // binders (so `{A B : Type}` counts as 2).
    int countLeadingImplicitArgumentNames(
        const SurfaceDefinitionDeclaration& declaration);

    // For each convention name registered in `conventionRegistry_`, check
    // whether it appears as a free identifier somewhere in `declaration`.
    // Collect a deterministic ordered list of "needed" conventions and
    // build implicit binders for each: one for the name itself, one for
    // each side-condition proposition. Returns a fresh
    // SurfaceDefinitionDeclaration with those binders prepended at the
    // front of `arguments`.
    SurfaceDefinitionDeclaration augmentDeclarationWithConventions(
        const SurfaceDefinitionDeclaration& declaration);

    // Walk `expression` and call `record(name)` for every
    // SurfaceIdentifier reference. Pattern definitions and `cases`
    // clauses' patterns introduce locally-bound names; we don't
    // currently model that here (the predicate is "appears anywhere",
    // not "appears free"), but the augment caller filters out names
    // the user explicitly binds, which handles the most common
    // shadowing case.
    template <typename Recorder>
    void collectMentionsInSurface(const SurfaceExpression& expression,
                                    Recorder record) {
        if (auto* id = std::get_if<SurfaceIdentifier>(&expression.node)) {
            record(id->qualifiedName);
            return;
        }
        if (auto* app = std::get_if<SurfaceApplication>(&expression.node)) {
            collectMentionsInSurface(*app->function, record);
            for (const auto& arg : app->arguments) {
                if (arg.value) collectMentionsInSurface(*arg.value, record);
            }
            return;
        }
        if (auto* pi = std::get_if<SurfacePiType>(&expression.node)) {
            if (pi->binder.type) {
                collectMentionsInSurface(*pi->binder.type, record);
            }
            if (pi->codomain) collectMentionsInSurface(*pi->codomain, record);
            return;
        }
        if (auto* lambda = std::get_if<SurfaceLambda>(&expression.node)) {
            if (lambda->binder.type) {
                collectMentionsInSurface(*lambda->binder.type, record);
            }
            if (lambda->body) collectMentionsInSurface(*lambda->body, record);
            return;
        }
        if (auto* let = std::get_if<SurfaceLet>(&expression.node)) {
            if (let->type) collectMentionsInSurface(*let->type, record);
            if (let->value) collectMentionsInSurface(*let->value, record);
            if (let->body) collectMentionsInSurface(*let->body, record);
            return;
        }
        if (auto* asc =
                std::get_if<SurfaceAscription>(&expression.node)) {
            if (asc->expression) {
                collectMentionsInSurface(*asc->expression, record);
            }
            if (asc->type) collectMentionsInSurface(*asc->type, record);
            return;
        }
        if (auto* bin =
                std::get_if<SurfaceBinaryOperation>(&expression.node)) {
            if (bin->left) collectMentionsInSurface(*bin->left, record);
            if (bin->right) collectMentionsInSurface(*bin->right, record);
            return;
        }
        if (auto* un =
                std::get_if<SurfaceUnaryOperation>(&expression.node)) {
            if (un->operand) collectMentionsInSurface(*un->operand, record);
            return;
        }
        if (auto* tup =
                std::get_if<SurfaceAnonymousTuple>(&expression.node)) {
            for (const auto& c : tup->components) {
                if (c) collectMentionsInSurface(*c, record);
            }
            return;
        }
        if (auto* cas = std::get_if<SurfaceCases>(&expression.node)) {
            if (cas->scrutinee) {
                collectMentionsInSurface(*cas->scrutinee, record);
            }
            for (const auto& clause : cas->clauses) {
                if (clause.body) {
                    collectMentionsInSurface(*clause.body, record);
                }
            }
            return;
        }
        // SurfaceNumericLiteral, SurfaceType, SurfaceProposition,
        // SurfaceSorry, SurfaceRing, calc, by_induction, and a handful
        // of other leaf/specialised nodes have no children we care
        // about for convention detection. We default to ignoring them
        // — at worst the convention doesn't fire for those forms.
    }

    // RAII guard that restores opacities flipped by `unfold X in …`
    // forms during a single definition / theorem's elaboration. The
    // guard runs after the body has been type-checked AND after
    // addDefinition completes (so the kernel's final check sees the
    // unfolded view); on exit it restores each affected definition
    // to its original opacity and truncates the pending-restores
    // list back to the pre-call size.
    struct OpacityRestoreScope {
        Elaborator& self;
        size_t startSize;
        explicit OpacityRestoreScope(Elaborator& s)
            : self(s),
              startSize(s.pendingOpacityRestores_.size()) {}
        ~OpacityRestoreScope() {
            bool anyRestored = false;
            while (self.pendingOpacityRestores_.size() > startSize) {
                const auto& entry =
                    self.pendingOpacityRestores_.back();
                auto it = self.environment_.declarations.find(
                    entry.first);
                if (it != self.environment_.declarations.end()) {
                    if (auto* def =
                            std::get_if<Definition>(&it->second)) {
                        def->opacity = entry.second;
                        anyRestored = true;
                    }
                }
                self.pendingOpacityRestores_.pop_back();
            }
            if (anyRestored) {
                // Reduction depends on opacity, and the kernel's WHNF /
                // isDefEq caches were populated during the just-finished
                // unfold scope under the now-stale transparent view.
                invalidateKernelCaches();
            }
        }
    };

    void elaborateDefinition(const SurfaceDefinitionDeclaration& origDecl);

    // Stage-1 elaboration of a theorem: elaborate the declared type (the
    // statement) only, then register it with a fixed placeholder body
    // (opaque, so it never unfolds) — the same shape `deriveInterfaceCache`
    // produces, but without ever touching the proof. The arguments-to-Pi
    // construction mirrors `elaborateDefinition`'s; for the pattern
    // (inductive) form `arguments` is empty and the whole signature lives in
    // `declaration.type`.
    void elaborateTheoremStatementOnly(
            const SurfaceDefinitionDeclaration& declaration);

    // -------- pattern-matching definitions --------
    //
    // A pattern-match definition like
    //
    //   definition Natural.add : Natural → Natural → Natural
    //     | zero,         m => m
    //     | successor(k), m => successor(Natural.add(k, m))
    //
    // is translated into a recursor call. For v1 the supported shape is:
    //   - All function arguments are listed in the type signature
    //     (Pi-chain). No `(arguments)` allowed before the colon.
    //   - The first argument is the scrutinee. Its type must be a bare
    //     inductive identifier with zero parameters (Natural, Boolean,
    //     enum-like types).
    //   - Other positions in each pattern row must be bare variable
    //     patterns (or `_`).
    //   - Every constructor must have exactly one matching case.
    //   - Recursive calls in case bodies must use the destructured
    //     argument of the case as their first argument (structural
    //     recursion).

    void elaboratePatternMatchDefinition(
        const SurfaceDefinitionDeclaration& declaration);

    struct FunctionArgumentPair {
        std::string name;
        SurfaceExpressionPointer surfaceType;
    };

    // Builds the kernel Lambda for one case of a pattern-match definition.
    // For parameterised inductives, the caller supplies the parameter
    // values that the scrutinee is applied to; the case lambda strips
    // the constructor's parameter Pis and substitutes the values into
    // the remaining argument types, so the case lambda binds only the
    // non-parameter arguments.
    // The `outerBinderStack` is the context of outer (pre-colon) binders
    // around the entire pattern-match definition. Non-scrutinee
    // argument types and the case body are elaborated with those
    // outer binders in scope, so they can be referenced by name.
    ExpressionPointer buildCaseLambda(
        const SurfaceDefinitionDeclaration& declaration,
        const std::string& constructorName,
        const std::string& inductiveName,
        const std::vector<LevelPointer>& inductiveUniverseArguments,
        ExpressionPointer motive,
        const std::vector<ExpressionPointer>& parameterValues,
        const std::vector<LocalBinder>& outerBinderStack);

    // Builds the body for one outer case of a pattern-match definition,
    // walking the user's pattern positions from `patternIndex` onwards.
    //
    //   * Bare-name positions are already regular case-lambda binders;
    //     we just skip past them.
    //   * Constructor patterns at non-scrutinee positions need to be
    //     destructured AND have all later-bound function-arg types
    //     refined under the destructure. We do this by emitting an
    //     inner recursor on that position, with a motive that abstracts
    //     both the position's variable AND all later position variables.
    //     The recursor's case lambda binds the constructor's value args
    //     plus a fresh re-binding of each later position (with refined
    //     types), and recursively calls back into this function for the
    //     next position.
    //
    // V1 restrictions for inner constructor patterns: the inner inductive
    // must be non-parameterised, non-indexed, single-constructor, and
    // non-recursive. (Real call sites — `IntegerRepresentative.make` —
    // satisfy all four; multi-constructor inner patterns would need
    // cross-row coverage analysis that isn't yet wired up.)
    ExpressionPointer buildBodyForCase(
        const SurfacePatternCase& matchedCase,
        size_t patternIndex,
        std::vector<size_t> positionToBinderIndex,
        std::vector<LocalBinder> currentLambdaBinders,
        std::vector<LocalBinder> bodyStack,
        ExpressionPointer expectedType,
        int outerBinderCount,
        const std::map<std::string, std::string>&
            recursiveArgToHypothesis,
        const std::string& declarationName);

    // Walks a surface expression and replaces calls of the form
    // `thisDeclName(<outerBinders>..., <destructuredName>, ...rest)`
    // with `<recursionHypothesis>(...rest)`, where the mapping
    // `destructuredName → recursionHypothesis` is determined by the
    // case currently being translated. `outerBinderCount` is the
    // number of pre-colon arguments the user must repeat in every
    // recursive call before the scrutinee. Non-recursive calls (or
    // recursive calls on something other than a destructured variable
    // at the right position) are left alone — the kernel will reject
    // them as ill-typed if structural recursion was actually required.
    SurfaceExpressionPointer rewriteRecursiveCalls(
        SurfaceExpressionPointer expression,
        const std::string& thisDeclName,
        const std::map<std::string, std::string>&
            recursiveArgToHypothesis,
        int outerBinderCount);

    void elaborateInductive(const SurfaceInductiveDeclaration& declaration);

    // -------- expression elaboration --------

    // Convert a list of SurfaceArguments (possibly with names) into a
    // positional list of SurfaceExpressionPointers, reordering named
    // arguments against the function's parameter-binder names. The
    // result is what the rest of the application-dispatch logic
    // expects (a positional vector).
    //
    // Rules:
    //   * If no argument has a name, return the values unchanged.
    //   * If any argument has a name, look up the function head's
    //     declaration in the environment and walk its kernel-Pi-chain
    //     `displayHint`s. The displayHints — minus the implicit-arg
    //     prefix the user's positional count implies — are the
    //     parameter names users can reference.
    //   * Positional arguments and named arguments may be mixed:
    //     positional arguments fill slots in order, named arguments
    //     take their named slot. Duplicate assignments are an error.
    //
    // On any inability to find the parameter names (head isn't a
    // direct identifier, declaration not in env, anonymous binders),
    // mixed positional+named falls back to positional-only by
    // requiring all arguments to be positional.
    std::vector<SurfaceExpressionPointer> reorderArgumentsForCall(
        const std::vector<SurfaceArgument>& arguments,
        SurfaceExpressionPointer functionSurface,
        int line);

    // RAII guard pushing an expected type onto goalStack_ at entry
    // and popping it on exit. Used by elaborateExpression so the
    // `goal` keyword can resolve to the most-recent active expected
    // type without each caller having to thread it through.
    struct GoalScope {
        std::vector<ExpressionPointer>& stack;
        bool pushed;
        GoalScope(std::vector<ExpressionPointer>& s,
                  ExpressionPointer expectedType)
            : stack(s), pushed(false) {
            if (expectedType) {
                stack.push_back(expectedType);
                pushed = true;
            }
        }
        ~GoalScope() {
            if (pushed) stack.pop_back();
        }
    };

    ExpressionPointer elaborateExpression(
        const SurfaceExpression& expression,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType = nullptr);

    // `by_strong_induction on E with subject, ih { body }` —
    // single-step strong induction. Extract the scrutinee's carrier
    // type, build `<CarrierTypeName>.strong_induction` as the
    // induction lemma, and dispatch to elaborateByInductionUsing.
    //
    // Carrier extraction: WHNF the scrutinee's type, peel
    // Application heads, expect a Constant at the spine. The
    // strong-induction lemma must live in the module that defines
    // the type and be named `<TypeName>.strong_induction`.
    ExpressionPointer elaborateByStrongInduction(
        const SurfaceByStrongInduction& form,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    // `choose <name> such that <predicate>;` — Exists-elim via scope
    // lookup. Scans local binders last-first for a hypothesis whose
    // type WHNFs to `Exists(T, motive)`; the most-recent match wins.
    // Desugars to a `cases ⟨<name>, _choice_pred_…⟩ => <body>` over
    // that hypothesis.
    //
    // v1: the user's predicate is documentation, not a search key —
    // if the most-recent Exists doesn't match what the user intended,
    // the body will fail to elaborate when it tries to use the
    // destructured predicate hypothesis. Predicate-shape filtering
    // is a planned follow-up.
    ExpressionPointer elaborateChoose(
        const SurfaceChoose& choose,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    // `by_induction on E using L with subject, ih { body }`:
    //   E    = local-variable scrutinee
    //   L    = induction lemma whose type is
    //              (motive : T → Sort u)
    //            → ((subject : T) → IH(subject) → motive subject)
    //            → (target : T) → motive target
    //   body = proves motive(subject), with subject and ih in scope
    //
    // Strategy: build the motive by abstracting expectedType over E,
    // apply the lemma to the motive (so the kernel substitutes it into
    // the remainder of the lemma's type), then decompose the
    // already-substituted type to extract the subject and ih binder
    // types. Then build the step lambda and finish the application.
    // Try-then-revert auto-generalize for the lemma-based induction path
    // (`by_strong_induction`, `by_induction … using`), mirroring the
    // `cases`/`by_induction` wrapper: on failure with scrutinee-dependent
    // in-scope hypotheses, retry with them reverted into the goal (and
    // re-introduced in the step body). Zero-regression — proofs that
    // elaborate without reverting take the first path.
    ExpressionPointer elaborateByInductionUsing(
        const SurfaceByInductionUsing& form,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    // Revert `deps` (scrutinee-dependent in-scope binders, outermost-
    // first) into the goal, wrap the body in matching lambdas, run the
    // ordinary lemma-based induction at the reverted goal, then apply the
    // actual hypotheses — the same generalize/reintroduce telescope
    // `elaborateCasesWithRefining` uses, for the lemma path.
    ExpressionPointer elaborateByInductionUsingReverted(
        const SurfaceByInductionUsing& form,
        const std::vector<std::string>& deps,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    ExpressionPointer elaborateByInductionUsingInner(
        const SurfaceByInductionUsing& form,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    // Step 2 of the structured-proof feature. Elaborates
    // `claim P [by Hint]` (and the bare-claim trailing form, where
    // the goal is the surrounding expectedType). Auto-fills the
    // hint's arguments by unifying its conclusion with the goal and
    // looking up any leftover binder values in local hypotheses.
    //
    // Limitations of v1:
    // - Disjunctive arms aren't elaborated yet (Step 4).
    // - `claim P` without `by` isn't elaborated yet (Step 5).
    // - Inter-slot dependencies: each slot's domain may reference
    //   outer slots that are bound by unification. Slots not bound
    //   by unification must be findable in local hypotheses by
    //   structural-type match.
    ExpressionPointer elaborateStructuredClaim(
        const SurfaceStructuredClaim& claim,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // Walks the Pi chain of `hintType`, unifies the conclusion with
    // `goalClosed`, fills remaining binders from local hypotheses,
    // and returns the resulting application of `hintTerm`. All
    // inputs and outputs are in closed-over-localBinders form.
    // Representation contract (WS8): `goalClosed` and the returned proof are
    // CLOSED over `localBinders` (BoundVariable indices, not FreeVariables).
    // `hintTerm`/`hintType` come in CLOSED too. Internally the unification
    // works on OPENED forms (openOverLocalBinders), but every value crossing
    // this boundary is closed — callers feed the result straight back into
    // closed-term assembly.
    ExpressionPointer autoFillHintForClaim(
        ExpressionPointer hintTerm,
        ExpressionPointer hintType,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/);

    // Step 3 of the structured-proof feature. Elaborates `given (P)`
    // to a BoundVariable pointing at the unique in-scope hypothesis
    // of type `P`. Errors on zero matches or on ambiguity.
    ExpressionPointer elaborateGiven(
        const SurfaceGiven& given,
        const std::vector<LocalBinder>& localBinders,
        int line, int /*column*/);

    // Contradiction: if the most-recent local binder is False, or
    // pairs with some other in-scope hypothesis to produce False
    // via h(h') (or h'(h)), close ANY goal via
    // `False.eliminate_proposition`.
    //
    // Restricted to the LAST local binder (cost 0 in the unified
    // cost model) as one of the pair — the mathematician's
    // convention is to write the contradictory fact as the
    // immediately-preceding `claim` and then conclude. Avoids
    // O(N²) pair search and the noise it would cause; the user
    // can always write the contradiction-introducing claim before
    // the close. Skipped if `False.eliminate_proposition` isn't
    // in scope or no local binders exist.
    ExpressionPointer tryContradiction(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/);

    // Disjunction introduction: when the goal is `Or(A, B)`, try
    // to prove `A` via the full auto-prover; if that succeeds, wrap
    // with `Or.introduceLeft`. Else try `B` and wrap with
    // `Or.introduceRight`. Left-biased — if both branches would
    // succeed, the left one wins.
    ExpressionPointer tryDisjunctionIntro(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line);

    // Unified named-fact representation. A fact carries a proof
    // term and that proof's type, plus a cost so the matcher tries
    // cheap facts first. Used by `tryContextFactMatch` to collapse
    // the old "(1) hypothesis match" and "(7) library scan"
    // strategies into one stream that doesn't care whether the
    // proof originated from a local binder or a top-level
    // declaration.
    struct ContextFact {
        int cost;
        std::string source;
        ExpressionPointer proofTerm;  // closed in current scope
        ExpressionPointer type;       // closed in current scope
    };

    std::vector<ContextFact> collectContextFacts(
        ExpressionPointer /*goalClosed*/,
        const std::vector<LocalBinder>& localBinders,
        uint64_t goalHash,
        uint64_t goalHashUnreduced);

    // Unified named-fact match. Iterates ALL in-scope facts (local
    // binders + library declarations) by cost; for each, tries
    // `autoFillHintForClaim` to fill any Pi-binders from the goal +
    // hypotheses and produce a term of the goal type. Subsumes the
    // old "direct hypothesis match" and "library scan" strategies.
    // Stronger per-candidate attempt for a library lemma matched to the
    // goal only by its conclusion: build `name(?, …, ?)` and run the full
    // goal-driven hole-inference + side-condition discharge path (the same
    // machinery `by <lemma>` uses). This is what lets an INEQUALITY step
    // close with no `by` when the closing lemma needs proof arguments —
    // e.g. a monotonicity law `a ≤ b → 0 ≤ c → a*c ≤ b*c` whose premises
    // already sit in the local context. `autoFillHintForClaim` only does a
    // purely structural match/discharge and misses these. Returns null on
    // any failure; the returned term is verified closed and defeq-to-goal.
    ExpressionPointer tryLemmaByConclusion(
        const std::string& name,
        ExpressionPointer lemmaType,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line);

    ExpressionPointer tryContextFactMatch(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line);

    // Unified equality fact representation. Both local-hypothesis
    // equalities and library-lemma equalities (after subexpression
    // match + instantiation) live here as already-ground
    // (lhs, rhs, carrier, proof) tuples in the current scope.
    // Cost-tagged so the bridge tries cheap facts first.
    struct ContextEquality {
        int cost;
        std::string source;
        ExpressionPointer lhs;
        ExpressionPointer rhs;
        ExpressionPointer carrierType;
        LevelPointer carrierLevel;
        ExpressionPointer proofExpr;
    };

    // Helper: walk goal subexpressions looking for library-lemma
    // matches; instantiate matched lemmas and append as ContextEquality
    // entries. Mirrors the old `tryLibraryRewriteBridge` walker's
    // safeguards (skip bare-BV subexprs and bare-BV patterns; only
    // Applications descended into).
    void collectLibraryEqualitiesAt(
        ExpressionPointer subexpr,
        const std::vector<LocalBinder>& localBinders,
        std::vector<ContextEquality>& out);

    std::vector<ContextEquality> collectContextEqualities(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/);

    // Unified context-equality bridge. For every equality in scope
    // (local or library, ground or instantiated), try rewriting the
    // goal by replacing one side with the other, recursing on the
    // rewritten goal. Replaces the two separate strategies (local
    // transport bridge and library-rewrite bridge) with one code
    // path so future migration of other strategies to the same
    // fact-stream model has a precedent. See TODO.md "Hammer
    // unification" for the broader plan.
    //
    // Walks structurally — recurses into Application children. Other
    // expression kinds (Pi, Lambda, Let, etc.) are walked only if
    // they're at the top, not descended; widening that is a follow-
    // up. Budget shared with both old bridges.
    ExpressionPointer tryContextEqualityBridge(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line, int budget);

    // Conjunction introduction: when the goal is `And(A, B)`,
    // recursively prove each conjunct via the same auto-prover
    // dispatch and combine with `And.introduction`. Strictly more
    // powerful than the library-scan path because each conjunct can
    // use the FULL auto-prover (not just structural hypothesis
    // match).
    //
    // Recursion guard: relies on `autoProveClaim`'s normal
    // termination — each recursive call has a strictly smaller goal
    // (A or B vs. A ∧ B), so no extra budget needed.
    ExpressionPointer tryConjunctionIntro(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line);

    // Transitivity bridge: if the goal is `H(a, c)` and
    // `<H>.transitive` exists in scope, perform a bounded BFS over
    // hypotheses of type `H(_, _)` to find a chain a → m1 → … → c,
    // then fold the chain into nested transitive applications.
    //
    // Pattern matching is STRUCTURAL (no WHNF on goal or hypothesis
    // types) — δ-reducing definitions like `Integer.LessOrEqual`
    // would unfold the named head and we'd lose `<head>.transitive`'s
    // lookup. `isDefinitionallyEqual` on individual subterms still
    // sees through reduction when comparing midpoints / endpoints.
    //
    // Each transitive call tries both hypothesis-arg orderings since
    // carriers differ in their transitive signature
    // (Natural's lemma takes `(b ≤ c) → (a ≤ b) → a ≤ c` while
    // Integer/Rational/Real's takes `(a ≤ b) → (b ≤ c) → a ≤ c`).
    //
    // BFS bounded by MAX_DEPTH (typical path lengths are 1–3).
    ExpressionPointer tryTransitivityBridge(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/);

    // Build `<transitiveName>(a, b, c, hAB, hBC)` (closed-form term)
    // with given a/b/c (opened) and hypothesis proofs (closed-form
    // terms in the current scope). Tries both hypothesis-arg
    // orderings since carriers differ in transitive signature.
    // Returns the first ordering that typechecks; nullptr if neither.
    ExpressionPointer buildTransitiveCall(
        const std::string& transitiveName,
        ExpressionPointer aOpened,
        ExpressionPointer bOpened,
        ExpressionPointer cOpened,
        ExpressionPointer hAB,
        ExpressionPointer hBC,
        const std::vector<LocalBinder>& localBinders);

    // Run autoProveCalcStep on an equality goal — gives the top-
    // level claim path access to reflexivity, single-position diff
    // with `Equality.congruence` wrapping, and AC rearrangement via
    // `ring`. Returns nullptr if the goal isn't an Equality or none
    // of those strategies close it. Cheap to attempt: failure is
    // fast (extractEqualityComponents throws immediately on non-
    // Equality types) and silent.
    ExpressionPointer tryAutoProveEqualityGoal(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line);

    // Step 5 of the structured-proof feature. `claim P` (no `by`)
    // resolves the goal by:
    //   1. Context fact match — unified iteration over local binders
    //      and library declarations; each becomes a (proofTerm, type,
    //      cost) tuple; sorted by cost; for each, autoFillHintForClaim
    //      fills any Pi-binders from goal + hypotheses. Subsumes the
    //      old "direct hypothesis match" and "library scan" — same
    //      code path for both local and library facts.
    //   2. Equality battery — when the goal is an Equality, run
    //      autoProveCalcStep (reflexivity, single-position diff with
    //      `Equality.congruence` wrapping, AC rearrangement via ring).
    //      No-op for non-equality goals.
    //   3. Transitivity bridge — for `H(a, c)` goals, BFS hypothesis
    //      graph and fold `<H>.transitive` applications.
    //   4. Conjunction introduction — when the goal is `And(A, B)`,
    //      recurse on each conjunct and combine via
    //      `And.introduction`.
    //   5. Disjunction introduction — when the goal is `Or(A, B)`,
    //      try `A` first, else `B`; wrap with `Or.introduceLeft` or
    //      `Or.introduceRight` accordingly.
    //   6. Contradiction — if the in-scope hypotheses contain False
    //      or a `(h : P, h' : Not(P))` pair, close any goal via
    //      `False.eliminate_proposition`.
    //   7. Unified equality bridge — rewrite via any in-scope
    //      equality (local hypothesis or library lemma matched at a
    //      goal subexpression) and recurse on the rewritten goal.
    // v1 skips universe-polymorphic candidates (no universe inference
    // yet) and does a linear scan (acceptable at current library size;
    // an indexed lookup is a planned follow-on).
    // Symmetry fallback. The goal is `x = y` (or `R(x, y)` for a relation
    // R that advertises a symmetry lemma): if the direct close fails, prove
    // the flipped goal `y = x` / `R(y, x)` and wrap it. Lets e.g. `0 = b`
    // close from a `b = 0` fact whose conclusion is stated the other way.
    // Sound only for symmetric relations — `=` always, plus any R with a
    // `<R>.symmetric` / `<R>_symmetric` lemma; order relations (≤/<) have
    // no such lemma and are left untouched. Guarded against flip-back.
    ExpressionPointer trySymmetryFlip(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line);

    // Representation contract (WS8): `goalClosed` is CLOSED over
    // `localBinders`; the returned proof is CLOSED over them too (a proof of
    // exactly `goalClosed`), or this throws an ElaborateError ("couldn't
    // close this goal", already math-shaped). Each `tryX` tactic owns the
    // closed↔opened conversions internally and hands back closed terms.
    ExpressionPointer autoProveClaim(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line,
        int transportBudget = 1);

    // Profiling variant: runs every tactic, records per-attempt
    // outcome (succeeded?, time, winner descriptor where meaningful),
    // emits one AutoProveRow at the end. Returns the first successful
    // proof so verification still behaves identically; subsequent
    // tactics still execute so we capture independent hit-rates and
    // can compare alternative orderings offline.
    ExpressionPointer autoProveClaimProfiling(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line,
        int transportBudget);

    // Print just the spine head of a goal expression — typically a
    // Constant name like "Equality" / "LessOrEqual" / "Natural.is_prime".
    // Falls back to "<sort>" / "<pi>" / "<lambda>" / "<bv>" / "<fv>"
    // for non-constant heads. Used by the auto-prover profiler.
    std::string goalHeadName(ExpressionPointer expression);

    // Elaborates `claim [P] by cases { in (A): body  in (B): body }`.
    // Strategy:
    //   1. Determine the goal (proposition P if given, else expected).
    //   2. Elaborate each arm's disjunctType.
    //   3. Find an in-scope hypothesis of type `Or armA armB` — that's
    //      the disjunction we case-split on.
    // `claim P by substitution` / `claim P by substituting <eq>` —
    // close the goal P via an equality bridge: find (or use the
    // supplied) equality `eq : a = b`, rewrite P along eq to a
    // related goal P', and find a proof of P' in the local context
    // or library. Sugar over `tryContextEqualityBridge` /
    // `Equality.transport_proposition` with better error messages
    // and (for the narrowed form) a smaller search space.
    ExpressionPointer elaborateClaimBySubstitution(
        const SurfaceStructuredClaim& claim,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line);

    //   4. Elaborate each arm body under an anonymous binder of its
    //      disjunct's type; build the two lambdas.
    //   5. Emit `Or.eliminate(A, B, Goal, leftLambda, rightLambda,
    //                          theInScopeDisjunction)`.
    // v1 limits: exactly 2 arms (binary disjunction).
    ExpressionPointer elaborateClaimByCases(
        const SurfaceStructuredClaim& claim,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line);

    // Elaborates a calc chain to a fold of Equality.transitivity calls.
    // Each step's proof is elaborated against the specific equality type
    // `Equality(carrier, previous, next)` so a type error points at the
    // failing step.
    //
    // For a single step the result is just the step proof (no transitivity
    // wrapper). For N ≥ 2 steps the result is left-folded:
    //   transitivity(... transitivity(transitivity(p1, p2), p3) ..., pN).
    // `calc` over a generic preorder relation R (e.g. `∣`, `⊆`): a chain
    // of `R` steps and `=` steps proving `R(first, last)`. Resolves R's
    // function and transitivity lemma from the carrier, folds the `R`
    // steps via transitivity, and absorbs interleaved `=` steps by
    // `Equality.transport_proposition`. All terms are closed-over-
    // localBinders form, like the rest of the elaborator.
    ExpressionPointer elaborateCalcPreorder(
        const SurfaceCalc& calc,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    ExpressionPointer elaborateCalc(
        const SurfaceCalc& calc,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    // Try to decompose `term` as `op(left, right)` where `op` is a
    // top-level Constant. Returns true with the op name, universe
    // arguments, and the two argument expressions on success.
    bool decomposeBinaryOpApplication(
        ExpressionPointer term,
        std::string& outOpName,
        std::vector<LevelPointer>& outOpUniverseArguments,
        ExpressionPointer& outLeft,
        ExpressionPointer& outRight);

    // Hook called after each theorem is added to the environment.
    // If the type fits the rewrite-lemma shape, registers it in
    // `lemmaIndex_` under both `spineHash(LHS)` and `spineHash(RHS)`
    // so the calc auto-prover can apply it in either direction.
    void registerAlgebraicShape(const std::string& theoremName,
                                  ExpressionPointer typeExpr);

    // Rewrite-lemma registration. If `typeExpr` has the shape
    //   Π x₁ : T₁. … Π xₙ : Tₙ. Equality.{u}(carrier, LHS, RHS)
    // *and* the theorem has no universe parameters (first-cut
    // limitation: universe-arg instantiation at use-site isn't wired
    // up yet), index the lemma under both `spineHash(LHS)` and
    // `spineHash(RHS)`. The reverse-direction entry lets the calc
    // auto-prover handle `subLeft = … RHS-shape …`, wrapping the
    // emitted proof in `Equality.symmetry`.
    //
    // We skip degenerate shapes: zero binders (the LHS would be
    // closed, which makes the matcher pointless), or an LHS that is a
    // bare BoundVariable (would match anything and is unlikely to be
    // a useful rewrite).
    void registerGenericRewriteLemma(const std::string& theoremName,
                                       ExpressionPointer typeExpr);

    // Auto-prover for unannotated calc steps. Given a calc step's
    // previous and next endpoints (both kernel terms in closed form),
    // try a small bag of strategies in priority order to construct a
    // proof of `Equality.{u}(carrier, previous, next)`. Returns
    // nullptr if none succeed; the caller then errors with a
    // "supply `by <reason>`" diagnostic.
    //
    // v0 strategies:
    //   1. Definitional equality via the kernel's isDefinitionallyEqual.
    //      Catches β/ι/δ reductions (e.g. `succ(b) + x` vs `succ(b+x)`).
    //
    // Future strategies (v1+):
    //   2. Single-position diff classified as commutativity /
    //      associativity / identity / local-hypothesis.
    //   3. Multi-position composition.
    // True if `expression` contains any FreeVariable node. Auto-prover
    // calc-step results are closed over the local binders (binders as de
    // Bruijn indices, top-level names as Constants), so a leftover
    // FreeVariable means the term was opened and not re-closed — a bug.

    // Validating wrapper around autoProveCalcStepRaw: a closedness
    // invariant check that turns a class of auto-prover bugs from cryptic
    // kernel rejections into loud, attributed warnings. The raw search is
    // supposed to return a CLOSED proof; if it leaks a free variable the
    // term is invalid and must not be used (see the body for details).
    ExpressionPointer autoProveCalcStep(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        ExpressionPointer stepEqualityType,
        int line, int column);

    // Prove `App(leftFn, leftArg) = App(rightFn, rightArg)` when BOTH the
    // function and the argument differ — the multi-position case the
    // single-position diff walker bails on (e.g. `a + c = b + d` from
    // `a = b`, `c = d`). Recursively prove each sub-equality, then combine
    //   leftFn leftArg = leftFn rightArg   (congruence, rewrite the arg)
    //   leftFn rightArg = rightFn rightArg (congruence, rewrite the fn)
    // joined by transitivity. The recursion bottoms out via
    // autoProveCalcStep on strictly smaller terms. Returns nullptr if
    // either sub-proof fails or a type/level can't be computed.
    ExpressionPointer proveApplicationDiff(
        const std::vector<LocalBinder>& localBinders,
        const Application* leftApp,
        const Application* rightApp,
        int line, int column);

    // One step of a single-position congruence descent: which side stayed
    // fixed (Arg keeps the function and varies the argument; Fn keeps the
    // argument and varies the function) and the fixed subterm.
    struct CalcCongruencePathStep {
        enum class Kind { Arg, Fn };
        Kind kind;
        ExpressionPointer savedSide;
    };

    // Wrap `proof : currentLeft = currentRight` from innermost out with one
    // `Equality.congruence` per path step (outermost step applied last),
    // reconstructing the full outer `= ` proof. The per-step domain/codomain
    // types are inferred in the local context and closed back over the local
    // binders — the OPEN→CLOSED splice that, done wrong, leaks an unbound
    // internal variable; kept in ONE place here. Returns nullptr if any
    // type/level inference fails. Shared by the goal-only walker
    // (autoProveCalcStepRaw) and the cited-proof applicator
    // (tryDiffApplyUserProof), which differ only in how they FIND the path
    // and the inner proof — the wrapping is identical.
    ExpressionPointer wrapCongruenceChainOutsideIn(
        const std::vector<LocalBinder>& localBinders,
        const std::vector<CalcCongruencePathStep>& pathStepsOutsideIn,
        ExpressionPointer currentLeft,
        ExpressionPointer currentRight,
        ExpressionPointer currentProof);

    ExpressionPointer autoProveCalcStepRaw(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        ExpressionPointer stepEqualityType,
        int line, int column);

    // Non-calc wrapper around tryDiffApplyUserProof. Extracts the
    // equality endpoints from `goalClosed` and dispatches to the same
    // single-position diff walker used inside calc steps. Returns the
    // wrapped proof (with type definitionally equal to `goalClosed`)
    // on success, nullptr if either the goal isn't an Equality, the
    // hint isn't an Equality, or the walker can't bridge them.
    // Speculative check: if the user wrote `congruenceOf(λ, P)` at a
    // non-calc position where bare `P` would also close the goal via
    // diff inference, warn that the wrapper is redundant. Mirrors the
    // calc-step detector at the `by` site. No-op unless
    // --check-redundant-by is on. `surfaceExpression` is the source
    // expression at the position whose expected type is
    // `expectedTypeClosed` (already-elaborated form).
    void checkRedundantCongruenceOfWrapper(
        const SurfaceExpressionPointer& surfaceExpression,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedTypeClosed,
        const std::string& positionLabel);

    // After elaborating a term with an expected type, retry with
    // diff-wrap if the inferred type doesn't subtype-match the
    // expected type and both are Equality types with a unique
    // single-position diff. Returns the (possibly wrapped) term, or
    // the original term unchanged on either match or failure. Cheap
    // when types already match (one infer + one isDefinitionallyEqual check).
    // WS8 contract guard for coerceToExpectedTypeViaDiff's diff
    // strategies. Each `tryX` helper is supposed to return either nullptr
    // ("didn't fire") or a term CLOSED over the local binders. A bug that
    // lets a bound variable escape (historically the symmetry-flip diff)
    // would pass silently here and die deep in the kernel as "bare
    // BoundVariable reached inferType". This turns that into an O(1)
    // check at the source: a non-closed result is rejected (warned about,
    // for the developer) and treated as "didn't fire", so coerce falls
    // back to the unwrapped term and the downstream authoritative check
    // reports a clean, math-shaped error instead of an internal crash.
    ExpressionPointer acceptCoercionIfClosed(
        ExpressionPointer wrapped,
        const std::vector<LocalBinder>& localBinders,
        const char* strategy) const;

    ExpressionPointer coerceToExpectedTypeViaDiff(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer expectedTypeClosed);

    // Coerce a Proposition-valued term into a proof of itself when
    // the term equals the expected type. Returns nullptr if either
    // (a) the term isn't of type Proposition, or (b) the term isn't
    // kernel-equal to the expected type. On match, runs the
    // auto-prover and returns the resulting proof — re-wrapping
    // any ElaborateError with a message keyed to the bare-
    // proposition slot so the user sees `couldn't prove `<P>` to
    // fill the argument` rather than a raw dispatch error.
    ExpressionPointer tryBarePropositionAsProof(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer termTypeOpened,
        ExpressionPointer expectedTypeClosed);

    // Classical LEM bridge — when `term : Not(Not(P))` and the goal
    // is `P`, wraps with `Logic.double_negation_eliminate(P, term)`.
    // Returns nullptr if the term's type isn't Not(Not(_)), if the
    // inner proposition doesn't match `expectedTypeClosed`, or if
    // `Logic.double_negation_eliminate` isn't in scope.
    //
    // `Not(X)` unfolds to `X → False` (definition in Logic.basics);
    // we WHNF on each layer so the structural match works whether
    // the term's type is spelled `Not(Not(P))` or `(P → False) →
    // False`.
    ExpressionPointer tryDoubleNegationElimination(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer termTypeClosed,
        ExpressionPointer expectedTypeClosed);

    // Walk two expressions in parallel through Application structure,
    // collecting every leaf-level position where they differ. A leaf
    // here is anything that isn't an Application — Constant, BV, FV,
    // Sort, Pi, Lambda, Let (we don't descend into binders). If all
    // collected diffs share the SAME pair (a, b) — i.e., the
    // expressions agree everywhere except at occurrences of a single
    // common subterm difference — return (a, b). Otherwise (no diff,
    // or multiple distinct diff pairs) return (nullptr, nullptr).
    //
    // This catches both:
    //   * "single-position diff" (one slot differs, like `f(a)` vs `f(b)`)
    //   * "abstract-all diff" (the same pair differs at multiple
    //     positions, like `g(a, a)` vs `g(b, b)` — diff is (a, b) at
    //     two slots).
    // It does NOT catch heterogeneous diffs (e.g., `(a, b)` vs `(b, a)`
    // — the elaborator can't synthesize a single bridging equation
    // for those).
    std::pair<ExpressionPointer, ExpressionPointer>
    findUniqueDiffPair(
        ExpressionPointer left, ExpressionPointer right);

    // When `term`'s inferred type doesn't match the expected type but
    // they differ at a unique single position by subterms (a, b), and
    // a `a = b` or `b = a` equation lives in the local context, wrap
    // `term` with `Equality.transport_proposition(λz. T_expected[b ↦ z],
    // a, b, eq_or_sym(eq), term)` so the user can write the term
    // naturally without an explicit `rewrite`.
    //
    // Search scope: local binders only (not library lemmas) — keeps
    // the check cheap on every type-coercion attempt.
    ExpressionPointer tryDiffBridgeViaContextEquality(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer termTypeClosed,
        ExpressionPointer expectedTypeClosed);

    // If `type` WHNFs to a class equality `Quotient.mk(T, R, x) =
    // Quotient.mk(T, R, y)`, return the underlying equivalence `R(x, y)`;
    // else nullptr. Used both by the equality-of-classes coercion and by
    // hole-filling (so a proof citing `R` fills its `?`s against `R(x, y)`
    // when the surrounding goal is the class equality). `type` is returned
    // in whatever representation it came in — sub-terms are extracted and
    // reassembled in place, so callers can stay in opened or closed form.
    // Components of a `Quotient.mk(T, R, rep)` class. `level` is the mk's
    // universe argument (null if absent).
    struct QuotientClassParts {
        ExpressionPointer carrier, relation, rep;
        LevelPointer level = nullptr;
    };

    // WHNF `endpoint` and peel `Quotient.mk(T, R, rep)` (three Application
    // layers, head `Quotient.mk`). The single shared mk-peeler — used by the
    // class-equality relaxer, the sound coercion, and the exact bridge.
    bool peelQuotientClass(ExpressionPointer endpoint, QuotientClassParts& out);

    ExpressionPointer relaxClassEqualityToEquivalence(ExpressionPointer type);

    // Equality-of-classes coercion (WS3). When a proof of the underlying
    // equivalence `R(x, y)` is supplied where an equality of quotient
    // classes `Quotient.mk(T, R, x) = Quotient.mk(T, R, y)` is expected,
    // wrap it in `Quotient.sound(T, R, x, y, proof)` — so proofs say "these
    // representatives are equivalent" and never name the quotient axiom.
    // The expected endpoints may be `construction` forms (e.g.
    // `Rational.fraction(...)`) that δ-reduce to `Quotient.mk`; WHNF exposes
    // the head. Returns nullptr unless the expected type really is an
    // equality of two `Quotient.mk` applications over the same (T, R) and
    // the term's type is definitionally `R(x, y)`.
    ExpressionPointer tryQuotientSoundForClassEquality(
            const std::vector<LocalBinder>& localBinders,
            ExpressionPointer term,
            ExpressionPointer termTypeClosed,
            ExpressionPointer expectedTypeClosed);

    // The `exact` bridge — the mirror of tryQuotientSoundForClassEquality.
    // When the goal is a quotient relation application `R(a, b)` and some
    // in-scope hypothesis proves `Quotient.mk(a) = Quotient.mk(b)` (the two
    // classes are equal — possibly written through `construction` forms that
    // δ-reduce to `mk`), discharge it with
    // `Quotient.exact.{u}(T, R, <equivalence instance>, a, b, h)` — so the
    // proof reads "since the classes are equal" and never names the axiom.
    // Scope (prototype): concrete-carrier quotients, where the carrier's
    // `IsEquivalenceRelation` instance is registered with no parameters and
    // no universe parameters (Integer/Rational/Real/PAdic/… reps); bails
    // otherwise. Only the forward direction (fact `mk a = mk b` for goal
    // `R a b`); a flipped fact is left to the symmetry-flip retry.
    // Resolve the registered `IsEquivalenceRelation(carrierT, relationR)`
    // instance, solving any leading instance parameters by unification —
    // e.g. `IntegerMod.equivalence(m)` for relation `CongruentModulo(m)`, or
    // `RingModulo.equivalence(c, m)` / `Group.*` cosets. Returns the instance
    // applied to the solved parameters, or nullptr (no instance / unsolved /
    // universe-polymorphic instance, which this path doesn't handle).
    // Returns the instance CLOSED over the local binders (ready to drop into
    // the exact term without further closeBack). `carrierT`/`relationR` are
    // OPENED (as the bridge holds them).
    ExpressionPointer resolveEquivalenceInstance(
            ExpressionPointer carrierT, ExpressionPointer relationR,
            const std::vector<LocalBinder>& localBinders);

    ExpressionPointer tryQuotientExactBridge(
            ExpressionPointer goalClosed,
            const std::vector<LocalBinder>& localBinders);

    ExpressionPointer tryDiffWrapForEqualityGoal(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer hintTerm,
        ExpressionPointer hintType,
        ExpressionPointer goalClosed);

    // Does `type` ultimately conclude in an `Equality(…)` after peeling
    // its leading Pi binders? Identifies a "pointwise" hypothesis like
    // `(i) → f(i) = g(i)` or `(i) → i ≤ n → f(i) = g(i)`.
    bool isPointwiseEqualityType(ExpressionPointer type);

    // Rewrite-under-a-binder. A calc `=` step whose endpoints are the SAME
    // function `F` applied to argument lists that differ in exactly one
    // position — a lambda (the binder body f vs g) — is a congruence under
    // that binder: it holds when `f(i) = g(i)` pointwise. Instead of the
    // author respelling both lambdas inside an
    // `F.extensional(…, λi.…, λi.…, λi.proof, …)` call, they write only the
    // per-index proof as the `by` step; `f`/`g` and all the shared
    // arguments are read off the endpoints.
    //
    // Generic over `F` and over the congruence lemma's argument order: we
    // look up `<F>.extensional` / `<F>.extensional_range` by convention,
    // apply it to the shared prefix + f + g, then fill its remaining
    // binders by walking them — the user's lambda goes to the unique
    // POINTWISE-equality binder (whatever its position), every other binder
    // is filled from the next shared suffix argument of `F`. So both
    // `Sum.extensional(r,f,g,pointwise,n)` and the range variant
    // `Sum.extensional_range(r,f,g,n,pointwise_range)` work unchanged.
    //
    // Returns nullptr unless the endpoints are a single-lambda-diff
    // application of a registered `F` and the proof elaborates pointwise —
    // so it never shadows an ordinary step proof.
    ExpressionPointer tryUnderBinderStep(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previous, ExpressionPointer next,
        const SurfaceExpression& proofSurface, int line, int column);

    // WS5 bounded combining. The single-position descent in
    // `tryDiffApplyUserProof` finds a proof only when the cited fact
    // bridges the calc step ALONE — one differing slot, matched forward
    // or symmetric. When the step has the cited fact in one slot AND
    // other differing slots that the *context* closes (the multi-position
    // case `a + c = b + d` from cited `a = b` with `c = d` in scope, or
    // the stepping-stone `a = c` from cited `a = b` with `b = c` in
    // scope), that descent bails. This fallback rewrites ONE endpoint by
    // the cited equation — `Equality.congruence` over every occurrence of
    // one of its sides — producing a stepping stone `mid`, then asks the
    // auto-prover to close the residual (`mid = next` or `prev = mid`)
    // FROM CONTEXT, and joins the two with `Equality.transitivity`. Every
    // term here is CLOSED over the local binders (de Bruijn indices),
    // matching `tryDiffApplyUserProof`'s representation contract; the
    // caller's coercion type-checks the result against the step type, so
    // any returned proof is sound by construction. Runs only on the
    // descent's failure path, so it adds no cost to steps that already
    // close. Returns nullptr if no attempt's residual closes.
    ExpressionPointer tryCombineCitedWithContext(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer userProof,
        ExpressionPointer userLeft,
        ExpressionPointer userRight,
        ExpressionPointer userCarrier,
        LevelPointer userCarrierLevel,
        int line, int column);

    // Given a user-supplied `by <equationProof>` for a calc `=` step,
    // see whether the proof's equation (a = b) sits at a unique
    // single-position diff between `previousKernel` and `nextKernel`.
    // If so, wrap with the chain of `Equality.congruence` calls to
    // produce a proof of `previousKernel = nextKernel`. Returns
    // nullptr on miss. Caller already verified the user proof's type
    // didn't directly match the step's expected type, so this is the
    // diff-inference fallback ("user wrote the equation, elaborator
    // finds the slot").
    ExpressionPointer tryDiffApplyUserProof(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer userProof,
        ExpressionPointer userProofType,
        int line, int column);

    // Phase-2 fallback: invoke the existing `ring` proof emitter on
    // the goal `Equality(carrier, previous, next)`. Handles
    // multi-position AC rearrangement that the single-position
    // walker bails on. Returns nullptr on miss (e.g., the goal
    // isn't a pure sum or pure product of the same multiset of
    // atoms).
    ExpressionPointer tryAcRearrangement(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        int line);

    // Phase 3 first-order matcher. Walks `pattern` (a lemma's LHS or
    // RHS, in closed-over-binders form) against `subject` (a term
    // from the calc step's diff position, in closed-over-local-binders
    // form). A BoundVariable in the pattern with index < binderCount
    // is treated as a metavariable: on first occurrence it binds to
    // the subject sub-term; on subsequent occurrences the new binding
    // must be `structurallyEqual` to the existing one. Non-BV
    // positions must match exactly (with `levelsDefinitionallyEqual`
    // for Sort levels and Constant universe arguments).
    //
    // On success, `bindings[i]` holds the value matched against the
    // lemma's binder with de Bruijn index `i` (so `bindings[0]` is the
    // innermost binder). On failure, `bindings` may be partially
    // populated; the caller treats that as "no match".
    //
    // `piDepth` tracks how many local Pi binders the matcher has
    // descended into during recursion. A pattern BV index < piDepth
    // refers to a descended Pi binder (must match the subject's BV
    // literally). A pattern BV index in [piDepth, piDepth +
    // binderCount) refers to lemma metavariable slot
    // `(index - piDepth)`.
    bool matchAgainstPattern(
        ExpressionPointer pattern,
        ExpressionPointer subject,
        int binderCount,
        std::vector<ExpressionPointer>& bindings,
        int piDepth = 0);

    // Does `expression` contain any BoundVariable in the half-open
    // range `[low, high)` (interpreted in expression's own scope)?
    // Used by matchAgainstPattern to detect when a candidate metavar
    // binding would reference a local Pi binder that won't survive
    // when the lemma is applied in the outer context.
    bool referencesAnyBoundInRange(
        ExpressionPointer expression, int low, int high,
        int currentDepth = 0);

    // Simultaneously substitute the matched bindings into a lemma's
    // LHS or RHS. The lemma's expression is in closed-over-binders
    // form: BoundVariable indices `0..bindings.size()-1` refer to the
    // lemma's metavariable binders; `bindings[i]` is the value for
    // BV(i), expressed in the *subject's* (calc-step) scope. The
    // result lives in the subject's scope.
    //
    // We do this in a single walk rather than chaining the kernel's
    // single-binder `substitute`. The chained-substitute approach
    // corrupts a binding's BoundVariable indices the second time the
    // walker passes over it: after substituting BV(0) → bindings[0],
    // a subsequent `substitute(_, 0, bindings[1])` walks the entire
    // tree (including bindings[0]) and decrements BV(>=1) — clobbering
    // bindings[0]'s outer-binder references. A single combined walk
    // sidesteps that by treating each binding as opaque once placed.
    // Emit an "unused name" warning when a binder a user explicitly
    // named (let, claim, suppose, choose, case … as, by_induction
    // with ih, etc.) is closed and the body it scopes over never
    // references it. The body is elaborated under the binder, so a
    // BV(0) inside `body` refers to the just-introduced name. Names
    // starting with '_' are anonymous (e.g. synthesised calc names)
    // and skipped. Gated by `--check-redundant-by` (default on).
    //
    // `form` is a short noun phrase describing where the binder came
    // from — embedded directly into the warning so the user knows
    // which surface construct to edit (e.g. "let binding",
    // "`case … as`", "`suppose … as`").
    void warnIfBinderUnused(
        const std::string& name,
        ExpressionPointer bodyUnderBinder,
        int line, int column,
        const char* form);

    // Variant taking an explicit relative BV index. Multi-binder
    // lambdas (`function (x : T) (y : U) => …`) push N binders
    // before elaborating the body, so binder i (0-based, outer-
    // first) is at BV(N - 1 - i) relative to that body.
    void warnIfBinderUnusedAtIndex(
        const std::string& name,
        ExpressionPointer bodyUnderBinders,
        int relativeIndex,
        int line, int column,
        const char* form);

    // Variant: check at the surface-AST level by walking the body
    // expression and looking for any `SurfaceIdentifier` referencing
    // `name`. Useful when the binder is introduced via a desugaring
    // (e.g. `choose N such that …;` builds a destructure) and we
    // don't have a clean post-elaboration body to inspect. False-
    // negatives are possible if the user shadows `name` inside the
    // body — that's tolerated; the warning is advisory.
    void warnIfSurfaceNameUnused(
        const std::string& name,
        const SurfaceExpression& body,
        int line, int column,
        const char* form);

    // True if `expression` contains any construct that hands the goal
    // to the auto-prover at elaboration time (`claim` in any of its
    // shapes — bare, with proposition, with `by cases`, with
    // substitution; `contradiction` likewise). Used by the `choose`
    // unused-name check: when the auto-prover runs inside the body,
    // it can consume any in-scope hypothesis, so a witness name `N`
    // bound by `choose N such that P(N);` is potentially used through
    // the anonymous P(N) hypothesis even if N never appears in the
    // body's surface tree.
    bool surfaceContainsAutoProverInvocation(
        const SurfaceExpression& expression);

    void emitUnusedNameWarning(
        const std::string& name, int line, int column,
        const char* form);

    bool surfaceMentionsName(
        const SurfaceExpression& expression,
        const std::string& name);

    // Whether `expression` references a BoundVariable at the relative
    // de Bruijn index `targetIndex` (counting outward from the
    // expression's enclosing scope). Used by `warnIfBinderUnused`
    // for the user-binder unused-name warning: after elaborating
    // the body, we check whether it has any BV(0) reference (i.e.
    // uses the just-introduced binder).
    bool referencesBoundVariable(
        ExpressionPointer expression, int targetIndex);

    // Whether every BoundVariable reference in `expression` that maps
    // to a lemma binder (relative index < bindings.size()) has a
    // non-null entry in `bindings`. Used by the precondition-discharge
    // pass in `tryLemmaIndexLookup` to know whether a binder type can
    // be safely instantiated yet, given only partial bindings.
    bool binderReferencesAllBound(
        ExpressionPointer expression,
        const std::vector<ExpressionPointer>& bindings,
        int nestedBinderDepth = 0);

    ExpressionPointer instantiateLemmaBinders(
        ExpressionPointer expression,
        const std::vector<ExpressionPointer>& bindings,
        int nestedBinderDepth = 0);

    // Phase 3 lemma-index lookup. Tries to close `subLeft = subRight`
    // (at a single calc-step diff position) using a registered rewrite
    // lemma. Subsumes the bespoke commutativity / associativity /
    // identity classifiers and additionally fires on arbitrary
    // user-written rewrite lemmas. Returns nullptr on miss; caller
    // falls through to the local-hypothesis path and then to the
    // Phase-2 AC-rearrangement fallback.
    ExpressionPointer tryLemmaIndexLookup(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer subLeft,
        ExpressionPointer subRight);

    // Try to prove `Equality(_, subLeft, subRight)` at a single
    // diff position. Strategies, in order:
    //   1. Lemma-index lookup (`tryLemmaIndexLookup`): bucket library
    //      rewrite lemmas by `spineHash(LHS)` and `spineHash(RHS)`,
    //      run a small first-order matcher on hits, emit the lemma
    //      application (wrapping in `Equality.symmetry` for reverse
    //      direction). Subsumes commutativity / associativity /
    //      identity / arbitrary user-written rewrite lemmas.
    //   2. Local hypothesis match: a binder of type
    //      `Equality(_, subLeft, subRight)` or its symmetric form is
    //      used directly (with a symmetry wrap on the symmetric case).
    // Returns nullptr on miss. Result is in CLOSED-over-localBinders
    // form.
    ExpressionPointer tryClassifyDiff(
        const std::vector<LocalBinder>& localBinders,
        const Context& openedContext,
        ExpressionPointer subLeft,
        ExpressionPointer subRight);

    // Legacy `?` hammer placeholder and its helpers (tryDirectHammer,
    // tryLocalHypothesisApplication, tryConstructorDisjointness,
    // tryContradictionFromHypotheses, elaborateHammerPlaceholder) have
    // been removed. Bare `claim P` / no-`by` `claim N : T;` /
    // `contradiction;` now flow through `autoProveClaim`, which
    // subsumes every strategy the hammer ran and goes well beyond it
    // (equality battery, transitivity bridge, conjunction / disjunction
    // intro, library scan, context-equality rewriting).
    // ----------------------------------------------------------------------
    // Commutative-ring decision tactic `ring`.
    //
    // v1 scope: handles pure-multiplication rearrangement. Both sides
    // of the goal `e1 = e2` must be products built from `<T>.multiply`
    // applied to atoms (anything not built from `<T>.multiply`). The
    // tactic reifies both sides as multisets of atoms, compares them,
    // and — on match — emits a proof using insertion-sort style swaps
    // (`<T>.multiply_commutative`) and associativity rewrites
    // (`<T>.multiply_associative`).
    //
    // Out of scope for v1: addition, distributivity, identity (1·x=x),
    // zero (0·x=0), negation, mixed sums-of-products. For those the
    // user keeps writing manual calc chains for now.
    //
    // Recognized carriers: any `T` whose head-Constant name has
    // `<T>.multiply`, `<T>.multiply_commutative`, and
    // `<T>.multiply_associative` in scope. We probe by lookup.

    // Flatten a kernel multiplication chain into a vector of factor
    // ExpressionPointers. Returns `false` if the term isn't a pure
    // product over the given carrier (e.g., contains a `<T>.add`).
    bool flattenRingProduct(
        ExpressionPointer term,
        const std::string& carrierOpName,
        std::vector<ExpressionPointer>& factorsOut);

    // Build a left-associated product `((f0 * f1) * f2) * ... * fn-1`
    // from a vector of factor kernel terms. Caller guarantees the
    // vector is non-empty.
    ExpressionPointer assembleLeftAssociatedProduct(
        const std::string& carrierMultiplyName,
        const std::vector<ExpressionPointer>& factors);

    // Total order on ExpressionPointers used to sort factor multisets
    // canonically. Compares by:
    //   1. node variant index
    //   2. variant-specific keys (de Bruijn index, name, etc.)
    //   3. children (for compound nodes)
    int compareExpressionStructure(
        ExpressionPointer left, ExpressionPointer right);

    // Z/p numerical fast-fail for `ring`. Walks `expression` treating
    // ring operations (.add / .multiply / .negate / .subtract) as
    // arithmetic over Z/p, and any other subexpression as an opaque
    // atom whose Z/p value is keyed off its bottom-up structural hash
    // (so the same atom on both sides maps to the same value).
    //
    // Sound as a one-sided filter: ring proves polynomial identities,
    // which hold in every commutative ring including Z/p. So if the
    // two sides disagree mod p, ring CANNOT succeed and we can bail.
    // Schwartz-Zippel: distinct polynomials of degree d disagree at
    // random points with probability >= 1 - d/p, which for p ~ 2^61 is
    // essentially 1 for any polynomial we'd see in a calc step.
    //
    // The carrier's add/multiply/etc. names are derived from the
    // carrier name; if any of them aren't recognised constants the
    // expression is treated as an atom.
    uint64_t evalRingMod(
        ExpressionPointer expression,
        const std::string& carrierName,
        const std::string& addName,
        const std::string& multiplyName,
        const std::string& negateName,
        const std::string& subtractName,
        const std::string& zeroName,
        const std::string& oneName,
        uint64_t modulus);

    // Returns true if both sides MIGHT be equal as polynomials (the
    // Z/p eval doesn't rule it out); false if Z/p says ring will fail.
    // Uses a Mersenne prime that fits in uint64_t.
    bool ringFastFailAgrees(
        ExpressionPointer leftEndpoint,
        ExpressionPointer rightEndpoint,
        const std::string& carrierName,
        const std::string& opNamespace);

    // `ring` — close an `e1 = e2` goal in a commutative ring.
    // v1: handles pure-multiplication rearrangement.
    // A node of a `linear_combination` combination tree, evaluated to the
    // equation it denotes: `left = right` witnessed by `proof`. A leaf is
    // either a hypothesis (an equality proof `a = b` → ⟨a, b, proof⟩) or a
    // scalar ring value `v` (the trivial equation `v = v`, witnessed by
    // reflexivity). The `+`/`*`/`-`/unary-`-` nodes combine their children
    // pointwise on each side, building the combined proof by two
    // single-argument congruences + transitivity (unary: one congruence).
    // All terms are in OPENED form (local binders as free variables); the
    // caller closes the assembled result once.
    struct CombinationEquation {
        ExpressionPointer left;
        ExpressionPointer right;
        ExpressionPointer proof;
    };

    CombinationEquation evalLinearCombinationTree(
        const SurfaceExpressionPointer& node,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        const std::string& opNamespace,
        const std::vector<ExpressionPointer>& structurePrefix,
        int line);

    // `linear_combination(e)` — close a commutative-ring equality goal
    // `goalL = goalR` from a combination `e` of equation hypotheses, when
    // the goal follows by ring algebra: check the bridge `goalL − goalR =
    // combL − combR` with the ring normaliser and assemble via
    // `Ring.equal_of_linear_combination`. `e` is a `+`/`*`/`-` tree whose
    // leaves are equality proofs (hypotheses) or scalar ring coefficients
    // (e.g. `c1 * h1 + c2 * h2`); a bare hypothesis is the single-leaf
    // case. v1 handles concrete carriers (the op/instance names resolve to
    // plain constants); a bundled carrier `Ring.carrier(s)` would need the
    // structure argument threaded (future).
    ExpressionPointer elaborateLinearCombination(
        const SurfaceLinearCombination& tactic,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    ExpressionPointer elaborateRing(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    // Prove `originalProduct = canonical` where `canonical` is the
    // left-associated product of `sortedFactors`. The original is
    // assumed to be some product over the same factor multiset; v1
    // proof: build the canonical kernel term as the target and let
    // the kernel verify definitional equality of the factor multiset
    // via a chain of multiply_associative + multiply_commutative.
    //
    // Simpler v1 approach: build proofs INSERTION-SORT style. Maintain
    // a "current" arrangement; at each step, find the position of the
    // next sorted factor in the current arrangement; commute it left
    // until in position. Each commute is a multiply_commutative
    // application wrapped in congruenceOf for the surrounding context.
    //
    // For now: if `originalFactors` already equal `sortedFactors`
    // element-wise (the goal is already canonical), emit reflexivity.
    // Otherwise (factors differ in order), defer to a fuller proof
    // generator — but emit an honest "not yet implemented" error.
    // Shift every BoundVariable in `expression` whose de-Bruijn index
    // is >= threshold up by `increment`. Used when embedding a kernel
    // term inside a new lambda binder.

    // Names of the ring axioms for one binary operation on a carrier.
    // For multiplicative use: ("Integer.multiply",
    // "Integer.multiply_associative", "Integer.multiply_commutative").
    // For additive use: same shape with `.add` instead of `.multiply`.
    struct RingAxiomNames {
        std::string op;            // e.g. "Integer.multiply"
        std::string associative;   // e.g. "Integer.multiply_associative"
        std::string commutative;   // e.g. "Integer.multiply_commutative"
    };

    // How `ring` reads a carrier's operations and laws. For a concrete
    // carrier the operation namespace is the carrier head itself
    // (`Integer.add`, `Integer.add_associative`) and there is no leading
    // structure argument. For the bundled commutative-ring carrier
    // `CommutativeRing.carrier(c)` the operations and laws live under
    // `CommutativeRing` and each carries `c` as its first kernel argument
    // (`CommutativeRing.add(c, …)`), captured as `structurePrefix`.
    struct RingScheme {
        std::string opNamespace;   // "Integer" | "CommutativeRing"
        std::string carrierHead;   // "Integer" | "CommutativeRing.carrier"
        std::vector<ExpressionPointer> structurePrefix;  // [] | [c]
    };

    RingScheme computeRingScheme(ExpressionPointer carrierType);

    // RAII: install a ring structure prefix for the duration of one ring
    // elaboration, restoring the previous value on scope exit (so nested
    // ring proofs and the normal empty-prefix concrete case are safe).
    struct RingStructurePrefixGuard {
        Elaborator& elaborator;
        std::vector<ExpressionPointer> saved;
        RingStructurePrefixGuard(
            Elaborator& e, std::vector<ExpressionPointer> prefix)
            : elaborator(e), saved(e.ringStructurePrefix_) {
            elaborator.ringStructurePrefix_ = std::move(prefix);
        }
        ~RingStructurePrefixGuard() {
            elaborator.ringStructurePrefix_ = std::move(saved);
        }
    };

    // Build a ring operation/law head: `makeConstant(name)` with the
    // active structure prefix (`[s]` for a bundled ring, empty for a
    // concrete carrier) applied first. So `ringConst("Ring.add")` yields
    // `Ring.add(s)` under a bundled ring and `Integer.add` (bare) under a
    // concrete one; callers then apply the operands as before.
    ExpressionPointer ringConst(const std::string& name);

    // Build `<op>(left, right)`.
    ExpressionPointer buildRingOp(
        const std::string& opName,
        ExpressionPointer left, ExpressionPointer right);

    // Build `<op>(left, right)` — alias kept for the old call sites in
    // case they're still around. (Should be replaced as call sites
    // migrate to the generalised form.)
    ExpressionPointer buildRingMultiply(
        const std::string& carrierName,
        ExpressionPointer left, ExpressionPointer right);

    // Build `Equality.transitivity.{u}(T, A, B, C, p1, p2)`.

    // Build `Equality.symmetry.{u}(T, A, B, p)` where p : A = B.

    // Build `Equality.congruence.{u, u}(T, T, λ : T → T, x, y, p)`
    // where p : x = y; returns proof of λ(x) = λ(y). Carrier and
    // codomain types are the same here (we only use it for ring-level
    // congruence).

    // Cross-carrier variant: lambda goes from sourceCarrier to
    // targetCarrier. Used when pushing a coercion through congruence.

    // Build `<axioms.associative>(P, a, b) : (P op a) op b =
    // P op (a op b)`.
    ExpressionPointer buildRingAssoc(
        const RingAxiomNames& axioms,
        ExpressionPointer P, ExpressionPointer a, ExpressionPointer b);

    // Build `<axioms.commutative>(a, b) : a op b = b op a`.
    ExpressionPointer buildRingCommute(
        const RingAxiomNames& axioms,
        ExpressionPointer a, ExpressionPointer b);

    // Build `reflexivity.{u}(T, x) : x = x`.

    // Build a proof : left_assoc(factors_with_swap) = left_assoc(factors).
    // Reading direction matches insertion-sort's chained proof: each
    // step's RHS is the freshly-rearranged form. `swapPosition` swaps
    // factors[swapPosition - 1] and factors[swapPosition]; result is
    // the proof of the new full product being equal to the previous.
    //
    // For positions just to the LEFT of swap, factors[0..swapPosition-2]
    // become the "prefix" P inside the proof; for positions just to
    // the RIGHT (swapPosition+1..n-1), each adds a congruenceOf-wrap
    // around the inner proof.
    //
    // Returns proof : left_assoc(factors) =
    //                 left_assoc(factors_after_swap)
    ExpressionPointer buildAdjacentSwapProof(
        const RingAxiomNames& axioms,
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        const std::vector<ExpressionPointer>& factors,
        size_t swapPosition);

    // Re-associate `expression` (an expression of `<Carrier>.multiply`s
    // and atoms) into left-associated form. Returns a proof of
    // `expression = left_assoc(flatten(expression))`.
    //
    // For the special case where the expression is already
    // left-associated, returns reflexivity.
    ExpressionPointer buildLeftAssocReassocProof(
        const RingAxiomNames& axioms,
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        ExpressionPointer expression);

    ExpressionPointer proveProductEqualsSorted(
        ExpressionPointer original,
        const std::vector<ExpressionPointer>& originalFactors,
        const std::vector<ExpressionPointer>& sortedFactors,
        const RingAxiomNames& axioms,
        ExpressionPointer carrierType,
        LevelPointer carrierUniverseLevel,
        int line);

    // =====================================================================
    // Ring normaliser — polynomial canonicalisation
    //
    // Decision procedure that extends the single-operator AC fast path
    // with distributivity, identity (0 and 1), and negation. Both sides
    // of `e1 = e2` are normalised to a sum-of-monomials over opaque
    // atoms; the atoms are keyed by subtree hash (so we compare by hash,
    // not by structural equality).
    //
    // A `monomialSignature` is the lex-sorted vector of factor hashes
    // appearing in a monomial (with multiplicity). A polynomial is a
    // `std::map<monomialSignature, signed coefficient>`, with the zero
    // coefficient entries omitted.
    //
    // The proof emitter restricts coefficients to {-1, 0, +1}. Goals
    // that, after distributivity, collect a like-term coefficient outside
    // that range (e.g. `a + a = 2 · a`) report a clear "not yet
    // supported" error rather than silently failing.
    // =====================================================================

    // One step in the embedding chain from the source of a numeric
    // literal (Natural, the source of every literal) up through
    // coercions to the goal carrier. Holds the coercion function name
    // plus the three preservation lemma names (zero, one, add) needed
    // to push the coercion through a sum-of-ones canonical form.
    //
    // "outer" refers to the target carrier of THIS step's coercion.
    // E.g. for `Natural.to_integer`: outer = Integer. For
    // `Integer.to_rational`: outer = Rational.
    struct RingEmbeddingStep {
        std::string coercionFunctionName;    // e.g. "Natural.to_integer"
        std::string zeroPreservesName;       // e.g. "Natural.to_integer.zero_preserves"
        std::string onePreservesName;        // e.g. "Natural.to_integer.one_preserves"
        std::string addPreservesName;        // e.g. "Natural.to_integer.add_preserves"
        // Target carrier names (the "outer" side of this coercion):
        std::string outerCarrierName;        // e.g. "Integer"
        ExpressionPointer outerCarrierType;
        LevelPointer outerCarrierUniverseLevel;
        std::string outerAddName;            // e.g. "Integer.add"
        std::string outerZeroName;           // e.g. "Integer.zero"
        std::string outerOneName;            // e.g. "Integer.one"
    };

    struct RingNormalisationContext {
        std::string carrierName;           // carrier HEAD, e.g. "Rational"
                                            // or "Ring.carrier" (bundle)
        ExpressionPointer carrierType;      // Constant("Rational") / Ring.carrier(s)
        LevelPointer carrierUniverseLevel;  // for Equality.* applications

        // Operation/law namespace and the IsRing instance. For a concrete
        // carrier `opNamespace == carrierName` (`Rational.add`,
        // `Rational.is_ring`); for the bundled carrier `Ring.carrier(s)`
        // it is `Ring` (`Ring.add`, `Ring.is_ring`) and every such term
        // carries `s` as its leading argument (the active
        // `ringStructurePrefix_`).
        std::string opNamespace;            // e.g. "Rational" / "Ring"
        std::string isRingName;             // "<opNamespace>.is_ring"

        std::string addName;                // "<opNamespace>.add"
        std::string multiplyName;           // "<carrier>.multiply"
        std::string negateName;             // "<carrier>.negate"
        std::string subtractName;           // "<carrier>.subtract"
        std::string zeroName;               // "<carrier>.zero"
        std::string oneName;                // "<carrier>.one"

        // Scalar-multiply operator names. The Integer is on the left
        // for `fromIntegerMultiplyName`, on the right for
        // `multiplyByIntegerName`. Empty when the carrier is Integer
        // itself (the scalar-by-integer case collapses into the
        // regular multiply path).
        std::string fromIntegerMultiplyName;
        std::string multiplyByIntegerName;

        // Embedding chain from the literal source (Natural) up to the
        // carrier. INNERMOST FIRST: chain[0] is always
        // "Natural.to_integer" (the literal-bearing step), chain[1]
        // is the next coercion up (e.g. "Integer.to_rational"), and
        // so on. Empty when carrier is Natural; length 1 for Integer;
        // length 2 for Rational; length 3 for Real.
        std::vector<RingEmbeddingStep> embeddingChain;

        // Atom table: hash → kernel expression. Filled lazily while
        // normalising. We trust 64-bit hashes — the canonicalisation is
        // sound even on a collision (different terms would happen to be
        // treated as the same atom, which would cause the polynomial
        // comparison to spuriously succeed for unequal goals — but the
        // proof emitter would then fail to produce a kernel-valid
        // proof, which the kernel catches at verification time).
        std::unordered_map<uint64_t, ExpressionPointer> atoms;
    };

    // A polynomial as map<signature, coefficient>, signature = sorted
    // vector of atom hashes (with multiplicity), coefficient = signed
    // integer.
    using RingMonomialSignature = std::vector<uint64_t>;
    using RingPolynomial = std::map<RingMonomialSignature, int>;

    // Drop zero-coefficient entries (caller is expected to call this
    // after any arithmetic that can produce a zero).
    void ringPolynomialCompact(RingPolynomial& polynomial);

    // polynomial += other, in place.
    void ringPolynomialAccumulate(
        RingPolynomial& polynomial,
        const RingPolynomial& other);

    // polynomial -= other, in place.
    void ringPolynomialSubtract(
        RingPolynomial& polynomial,
        const RingPolynomial& other);

    // Negate every coefficient.
    void ringPolynomialNegate(RingPolynomial& polynomial);

    // result := left · right (full pointwise distribute).
    RingPolynomial ringPolynomialMultiply(
        const RingPolynomial& left, const RingPolynomial& right);

    // Construct the polynomial representing `1` (single constant
    // monomial with empty factor list and coefficient 1).
    RingPolynomial ringPolynomialOne();

    // Construct the polynomial representing a single atom (one monomial
    // with one factor and coefficient 1). Side effect: register the atom
    // in `context.atoms` keyed by its hash.
    RingPolynomial ringPolynomialAtom(
        RingNormalisationContext& context, ExpressionPointer atom);

    // Recognise `<context.opName>(left, right)` and produce (left,
    // right). Returns true on a match.
    // Peel an application spine into (head, args), args outermost-LAST
    // (i.e. in source order). `head` is the innermost function.
    void peelSpine(ExpressionPointer expression,
                   ExpressionPointer& headOut,
                   std::vector<ExpressionPointer>& argsOut);

    // Check that the leading `ringStructurePrefix_` arguments of `args`
    // match the active structure prefix (for a bundled ring, `[s]`).
    // Empty prefix (concrete carrier) trivially matches.
    bool structurePrefixMatches(
        const std::vector<ExpressionPointer>& args);

    // Recognise `<opName>([prefix,] left, right)` (the structure prefix
    // is the leading bundle argument for a bundled ring, absent for a
    // concrete carrier) and produce (left, right).
    bool matchBinaryRingOp(
        ExpressionPointer expression,
        const std::string& opName,
        ExpressionPointer& leftOut,
        ExpressionPointer& rightOut);

    // Recognise `<negateName>([prefix,] inner)` and produce `inner`.
    bool matchUnaryRingNegate(
        ExpressionPointer expression,
        const std::string& negateName,
        ExpressionPointer& innerOut);

    // True if `expression` is `<zeroName>` (concrete) / `<zeroName>(s)`
    // (bundled ring: the constant applied to the structure prefix).
    bool matchRingZero(ExpressionPointer expression,
                          const std::string& zeroName);

    // True if `expression` is `<oneName>` / `<oneName>(s)`.
    bool matchRingOne(ExpressionPointer expression,
                         const std::string& oneName);

    // True if `expression` is a Natural literal `successor^k(zero)`
    // for some k >= 0. Sets `value` to k on match.
    bool tryParseNaturalLiteral(
        ExpressionPointer expression, int& value);

    // Recognise the carrier's idiom of a Natural literal: the
    // chain of coercions wrapping `successor^k(zero)`. The chain is
    // determined by `context.embeddingChain` (innermost first); we
    // peel off coercions outermost-first to reach the Natural literal.
    //
    // For Integer carrier: chain = [Natural.to_integer], so we expect
    //   Natural.to_integer(succ^k(zero)).
    // For Rational: chain = [Natural.to_integer, Integer.to_rational],
    //   so we expect Integer.to_rational(Natural.to_integer(succ^k(zero))).
    // For Real: one more layer of Rational.to_real(...) on top.
    //
    // At each level, BEFORE peeling the coercion, we also accept the
    // current outer carrier's named `zero` / `one` constants directly
    // (since `(0 : T)` and `(1 : T)` may δ-reduce to `T.zero` / `T.one`
    // during elaboration via the existing preservation lemmas, and the
    // kernel produces a structurally-different term than the unfolded
    // coercion application).
    bool tryParseCarrierEmbeddedNaturalLiteral(
        ExpressionPointer expression,
        const RingNormalisationContext& context,
        int& value);

    // Populate context.embeddingChain and scalar-multiply operator
    // names based on context.carrierName. Caller has already filled in
    // the carrier names (add, multiply, etc).
    void populateRingEmbeddingChain(RingNormalisationContext& context);

    // Build the Natural-level kernel for `successor^k(zero)`.
    ExpressionPointer buildNaturalLiteralKernel(int value);

    // Convert a kernel expression to a RingPolynomial, registering
    // opaque subterms as atoms along the way. Recursive: add /
    // multiply / negate are unfolded; zero and one are bottomed out;
    // everything else is an atom.
    RingPolynomial normaliseToRingPolynomial(
        ExpressionPointer expression, RingNormalisationContext& context);

    // Match `R.from_integer_multiply(n, x)` or
    // `R.multiply_by_integer(x, n)` against `expression`. On success,
    // sets `scalarOut` to the Integer-typed scalar argument,
    // `atomOut` to the carrier-typed argument, and `scalarOnLeftOut`
    // to true iff the operator put the scalar on the left (which
    // δ-unfolds to `(n : R) * x` rather than `x * (n : R)`).
    bool tryParseScalarMultiplyOperator(
        ExpressionPointer expression,
        const RingNormalisationContext& context,
        ExpressionPointer& scalarOut,
        ExpressionPointer& atomOut,
        bool& scalarOnLeftOut);

    // Wrap `scalarInteger` (a kernel expression of type Integer) with
    // the carrier's "outer coercion chain past Integer" to produce its
    // canonical form at the carrier. For Rational: returns
    //   Integer.to_rational(scalarInteger).
    // For Real: returns
    //   Rational.to_real(Integer.to_rational(scalarInteger)).
    // For Integer carrier (chain length 1): returns scalarInteger as-is.
    ExpressionPointer buildCoercedScalarForCarrier(
        ExpressionPointer scalarInteger,
        const RingNormalisationContext& context);

    // Build the kernel expression for `1 + 1 + ... + 1` with N copies
    // of `<context.oneName>`, left-associated.  N must be >= 1.
    ExpressionPointer buildRingCoefficientExpression(
        int count, const RingNormalisationContext& context);

    // Build the kernel expression for one monomial in canonical form.
    // Coefficient must be non-zero. Factors is the sorted signature.
    // The shape is:
    //    coefficientExpr * (factor_0 * factor_1 * ... * factor_{n-1})
    // with the inner product left-associated. If |coefficient| == 1,
    // we drop the `coefficientExpr *` prefix (with a `negate` wrap if
    // the coefficient is negative). If the factor list is empty, the
    // monomial is just `coefficientExpr` (possibly negated).
    ExpressionPointer buildCanonicalMonomial(
        const RingMonomialSignature& factors,
        int coefficient,
        const RingNormalisationContext& context);

    // Build the canonical-form kernel expression for a polynomial.
    // Empty polynomial → `zero`. Each entry (sig, coef) contributes
    // |coef| copies of the unit monomial; the whole polynomial is
    // the left-associated sum of all unit monomials in std::map sig
    // order. So [{x}:2, {y}:1] canonicalizes to ((x + x) + y), not
    // ((1+1)*x + y) — every monomial in the canonical form has
    // coefficient ±1.
    ExpressionPointer buildCanonicalPolynomial(
        const RingPolynomial& polynomial,
        const RingNormalisationContext& context);

    // Compare two polynomials for equality (canonical-form match).
    bool ringPolynomialsAgree(
        const RingPolynomial& left, const RingPolynomial& right);

    // =====================================================================
    // Ring normaliser — proof-emitter helpers.
    //
    // The decision step already canonicalises both endpoints to the same
    // polynomial. The emitter produces a proof of
    //     leftEndpoint = canonical(polynomial) = rightEndpoint
    // by recursive descent on each endpoint's kernel structure. At each
    // node (add/multiply/negate) the recursive sub-proofs are joined via
    // congruence, and a "merge" step reconciles the canonical-of-parts
    // form with the canonical-of-whole form.
    //
    // Coefficient guard: |coeff| <= 1 throughout. Larger collected
    // coefficients (e.g. a + a → 2·a) are out of scope for v2 and the
    // top-level decision step bails with a clear error before we reach
    // the proof emitter.
    // =====================================================================

    // ------------------------------------------------------------------
    // The ring laws `ring` depends on.
    //
    // `ring` proves a commutative-ring identity by normalising both
    // sides to a canonical sum-of-monomials and emitting a kernel proof
    // that chains the library's ring laws. Every law it can cite is named
    // below; if a goal needs a law the carrier doesn't provide, `ring`
    // fails with "carrier X is missing axiom Y". The laws come in two
    // flavours (see CLAUDE.md "Ring lemmas: foundational vs. derived"):
    //
    //   FOUNDATIONAL — the IsRing axioms, proved per carrier and looked
    //   up by name `<carrier>.<law>`:
    //     add_associative, add_commutative,
    //     multiply_associative, multiply_commutative,
    //     distributivity_left, distributivity_right,
    //     zero_add / add_identity_left   (0 + a = a),
    //     add_zero / add_identity_right  (a + 0 = a),
    //     one_multiply / multiply_identity_left   (1 · a = a),
    //     multiply_one / multiply_identity_right   (a · 1 = a),
    //     add_negate_left  (-a + a = 0), add_negate_right (a + -a = 0),
    //     negate_negate (-(-a) = a), negate_add (-(a+b) = -a + -b).
    //   (Library carriers split on the identity-law spelling:
    //   Rational/Real/PAdic use `zero_add`/`add_zero`/…; Integer uses
    //   `add_identity_left`/…. `pickAxiomName` probes both.)
    //
    //   DERIVED — consequences of IsRing, NOT restated per carrier.
    //   `ring` cites the abstract forms over a generic `IsRing` from
    //   `Algebra/ring_lemmas.math`, applied to the carrier's `is_ring`
    //   instance (see `buildAbstractRingLemmaApplication`):
    //     Ring.zero_multiply (0·a = 0), Ring.multiply_zero (a·0 = 0),
    //     Ring.multiply_negate_left (-a·b = -(a·b)),
    //     Ring.multiply_negate_right (a·-b = -(a·b)).
    //   A per-carrier `<carrier>.<law>` wrapper, if present, is used
    //   instead (Integer ships rep-level reflexivity proofs that are
    //   cheaper than the abstract derivation).
    //
    // Operation terms (`<carrier>.add`, `.multiply`, `.negate`,
    // `.subtract`, `.zero`, `.one`) are recognised and built by the
    // matchers/builders below.
    //
    // The names are resolved relative to an "operation namespace" and an
    // optional "structure prefix" (see `computeRingScheme` /
    // `ringStructurePrefix_`): for a concrete carrier the namespace is
    // the carrier head (`Integer`) with no prefix; for a bundled
    // commutative-ring carrier `CommutativeRing.carrier(c)` the namespace
    // is `CommutativeRing` and the prefix is `[c]`, so e.g.
    // `add_associative` resolves to `CommutativeRing.add_associative`
    // cited as `CommutativeRing.add_associative(c, …)`. A plain
    // `Ring.carrier(s)` is NOT a `ring` target — `ring` is a commutative-
    // ring tactic and a bare ring has no `multiply_commutative`.
    // ------------------------------------------------------------------
    struct RingLawNames {
        std::string addZeroRight;          // a + 0 = a
        std::string zeroAddLeft;           // 0 + a = a
        std::string multiplyOneRight;      // a * 1 = a
        std::string oneMultiplyLeft;       // 1 * a = a
        std::string multiplyZeroLeft;      // 0 * a = 0
        std::string multiplyZeroRight;     // a * 0 = 0
        std::string addNegateRight;        // a + -a = 0
        std::string addNegateLeft;         // -a + a = 0
        std::string negateNegate;          // -(-a) = a
        std::string negateAdd;             // -(a + b) = -a + -b
        std::string multiplyNegateLeft;    // -a * b = -(a * b)
        std::string multiplyNegateRight;   // a * -b = -(a * b)
        std::string distributivityLeft;    // a * (b + c) = a*b + a*c
        std::string distributivityRight;   // (a + b) * c = a*c + b*c
        std::string addAssociative;
        std::string addCommutative;
        std::string multiplyAssociative;
        std::string multiplyCommutative;
    };

    std::string pickAxiomName(const std::string& candidateOne,
                                 const std::string& candidateTwo);

    RingLawNames resolveRingLawNames(
        const std::string& opNamespace);

    void demandAxiomName(const std::string& axiomName,
                            const std::string& description,
                            const std::string& carrierName);

    // Build `<negateName>(inner)`.
    ExpressionPointer buildRingNegate(
        const std::string& negateName, ExpressionPointer inner);

    // Render a signed-monomial pair `(signature, sign)` to its canonical
    // kernel form. Just an alias for buildCanonicalMonomial.
    ExpressionPointer buildSignedMonomialKernel(
        const RingMonomialSignature& signature,
        int sign,
        const RingNormalisationContext& context);

    struct SignedMonomial {
        RingMonomialSignature signature;
        int sign;  // +1 or -1
    };

    // Explode each polynomial entry (sig, coef) into |coef| unit
    // signed monomials, each with sign = sign(coef). The canonical
    // form of a polynomial is a left-associated sum of these unit
    // monomials, so coefficient k > 1 shows up as k repeated
    // (sig, ±1) entries rather than as a `(1+1+...+1) * factors`
    // product. This keeps proof generation in proveAddMerge etc.
    // sign-agnostic: each entry is always ±1, and group-merging is
    // just "this signature has p positives and q negatives, net
    // (p - q) of sign sign(p - q), with min(p, q) cancel pairs".
    std::vector<SignedMonomial> polynomialToSignedMonomials(
        const RingPolynomial& polynomial);

    // Left-associated sum of kernel summands. summands must be non-empty.
    ExpressionPointer assembleLeftAssociatedSum(
        const std::string& addName,
        const std::vector<ExpressionPointer>& summands);

    // ----------------------------------------------------------------
    // Sum-AC building blocks: re-using v1's flatten/reassoc/sort
    // machinery but on the additive operator. Each "atom" of the sum
    // is an opaque kernel expression (a fully-rendered signed monomial).
    // ----------------------------------------------------------------

    // Re-associate `expression` (an arbitrary tree of `<addName>` and
    // opaque leaves) into a left-associated sum and return a proof
    // `expression = leftAssoc(flatten(expression))`.
    ExpressionPointer reassociateSumLeftProof(
        ExpressionPointer expression,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // Insertion-sort proof on a left-associated sum: given the original
    // factor list and the desired (sorted) factor list, produces a
    // proof `leftAssoc(originalFactors) = leftAssoc(sortedFactors)`.
    ExpressionPointer sortSumLeftAssocProof(
        const std::vector<ExpressionPointer>& originalFactors,
        const std::vector<ExpressionPointer>& sortedFactors,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // Same as sortSumLeftAssocProof but using the multiplicative
    // operator. Used by proveMultiplyMerge to sort factors within a
    // monomial.
    ExpressionPointer sortMultiplyLeftAssocProof(
        const std::vector<ExpressionPointer>& originalFactors,
        const std::vector<ExpressionPointer>& sortedFactors,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // Same as reassociateSumLeftProof but on the multiplicative
    // operator.
    ExpressionPointer reassociateMultiplyLeftProof(
        ExpressionPointer expression,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // ----------------------------------------------------------------
    // Top-level recursive descent and merge steps.
    // Each merge takes already-canonical operand polynomials and emits
    // a proof reconciling `(canonicalLeft) op (canonicalRight)` with
    // `canonical(leftPoly op rightPoly)`.
    // ----------------------------------------------------------------

    // ----------------------------------------------------------------
    // proveEqualsCanonical: recursive descent producing a kernel proof
    // `expression = canonical(polynomial(expression))`.
    // ----------------------------------------------------------------
    ExpressionPointer proveEqualsCanonical_impl(
        ExpressionPointer expression,
        RingNormalisationContext& context,
        const RingLawNames& axiomNames,
        RingPolynomial& polynomialOut);

    // Build the canonical kernel form of "k copies of `oneName` added,
    // left-associated" — the standard polynomial canonical form for
    // the constant polynomial `[{}: k]`. For k = 0 returns `zeroName`.
    ExpressionPointer buildSumOfOnesKernel(
        int k,
        const std::string& addName,
        const std::string& zeroName,
        const std::string& oneName);

    // Step 0 of the chain (Natural→Integer flavor): prove
    //   step.coercion(successor^k(zero)) = c_k
    // where c_k = `step.outerOne + step.outerOne + ... + step.outerOne`
    // (k copies, left-associated; or `step.outerZero` for k = 0).
    //
    // This uses the Natural-source shape where the literal is
    // successor^k(zero) and add_preserves' LHS exploits the kernel
    // reduction succ^j(zero) + succ(zero) ≡ succ^{j+1}(zero).
    ExpressionPointer proveNaturalLiteralPushThroughStep(
        int literalValue,
        const RingEmbeddingStep& step);

    // Push a coercion through a "k copies of innerOne added" canonical:
    //   step.coercion(innerOne + innerOne + ... + innerOne) = outerOne + ... + outerOne
    // (or step.coercion(innerZero) = outerZero for k = 0).
    // `innerAddName` is the add operator of the inner carrier;
    // `innerOneName` is its one constant.
    //
    // The inductive step at j is analogous to proveNaturalLiteral... but
    // operates on the literal `innerCanonical_j + innerOne` form,
    // without any successor-side kernel reductions.
    ExpressionPointer proveCoercionThroughSumOfOnes(
        int literalValue,
        const RingEmbeddingStep& step,
        const std::string& innerAddName,
        const std::string& innerZeroName,
        const std::string& innerOneName);

    // Prove `<chain>(successor^k(zero)) = canonical_k` where:
    //   - chain[0] is Natural.to_integer (always present for non-empty
    //     chains)
    //   - subsequent steps push through Integer→Rational, Rational→Real
    //   - canonical_k uses the OUTERMOST step's outer add/zero/one
    //
    // Used by the literal-detection branch of proveEqualsCanonical_impl
    // when the goal's carrier is Integer, Rational, or Real.
    ExpressionPointer proveIntegerLiteralEqualsCanonical(
        int literalValue, const RingNormalisationContext& context);

    ExpressionPointer proveEqualsCanonical(
        ExpressionPointer expression,
        RingNormalisationContext& context,
        const RingLawNames& axiomNames,
        RingPolynomial& polynomialOut);

    // ----------------------------------------------------------------
    // proveAddMerge: prove
    //   canonical(leftPoly) + canonical(rightPoly) = canonical(leftPoly + rightPoly)
    // ----------------------------------------------------------------
    //
    // Cases by emptiness of inputs:
    //   * Both empty:  LHS = zero + zero, RHS = zero. Not currently
    //     supported (would need a zero_add or add_zero step). We bail.
    //   * leftPoly empty: LHS = zero + canonical(rightPoly), RHS = canonical(rightPoly).
    //     Use zero_add (a.k.a. add_identity_left).
    //   * rightPoly empty: symmetric.
    //   * Both non-empty: full sum-AC sort + cancel.
    ExpressionPointer proveAddMerge(
        const RingPolynomial& leftPoly,
        const RingPolynomial& rightPoly,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // Prove `leftAssoc(combinedKernels) = canonical(mergedPoly)` for a
    // flat list of signed monomials, SORTING into canonical order and
    // CANCELLING opposite-sign like-term pairs (and keeping same-sign
    // duplicates, which match a coefficient>1 canonical entry). Shared
    // by the additive merge and the multiplicative merge's final phase
    // (so a product expansion `(a+b)(a-b)` whose cross terms cancel is
    // handled the same way a sum's like terms are). `combinedMonomials`
    // and `combinedKernels` are parallel; `mergedCanonical` is
    // `canonical(mergedPoly)`.
    ExpressionPointer proveSignedMonomialSumEqualsCanonical(
        const std::vector<SignedMonomial>& combinedMonomials,
        const std::vector<ExpressionPointer>& combinedKernels,
        const RingPolynomial& mergedPoly,
        ExpressionPointer mergedCanonical,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // ----------------------------------------------------------------
    // proveMultiplyMerge: prove
    //   canonical(leftPoly) * canonical(rightPoly) = canonical(leftPoly * rightPoly)
    // ----------------------------------------------------------------
    //
    // Strategy (full distribution):
    //   1. Fully distribute the product into a sum of monomial-products.
    //      We expand `(L_1 + ... + L_p) * (R_1 + ... + R_q)` via repeated
    //      distributivity_right / distributivity_left.
    //   2. Each summand `L_i * R_j` is then sign-pushed (multiply_negate_*
    //      + negate_negate) so its outer wrapper is at most one negate,
    //      and its factor product is left-associated.
    //   3. Sort factors within each summand by hash signature.
    //   4. Sort the summands by canonical order (per std::map merge).
    //   5. Cancel any (M, -M) pairs that arise.
    //
    // To stay implementable, the merge currently restricts to
    // the case where the EXPANSION DOES NOT PRODUCE CANCELLATION: i.e.
    // each pair of input monomials L_i × R_j yields a distinct merged
    // signature. (Cancellations would arise only when distinct L*R pairs
    // happen to produce identical signatures with opposite signs — rare
    // in our test set.)
    //
    // Implementation in steps:
    //   * Determine the canonical merged poly = leftPoly · rightPoly.
    //   * The "naive expanded form" is the left-associated sum
    //       (L_1·R_1) + (L_1·R_2) + ... + (L_p·R_q)
    //     (in lexicographic L-then-R order). For SINGLE-element leftPoly
    //     OR single-element rightPoly this collapses cleanly.
    //   * For each row i we use distributivity_right to peel
    //       (L_i + rest) * R = L_i*R + rest*R     (rest is left side of L)
    //     then recurse. Symmetric for the inner with distributivity_left.
    //
    // We handle:
    //   (a) Both single-summand: just product-of-monomials path.
    //   (b) Left single, right multi: distributivity_left, then per-
    //       summand monomial canonicalisation.
    //   (c) Left multi, right single: distributivity_right.
    //   (d) Left multi, right multi: distributivity_right peels one row
    //       at a time, recursing.
    // Helper: apply a derived ring lemma (one that follows from
    // IsRing's axioms — zero_multiply, multiply_zero,
    // multiply_negate_left, multiply_negate_right, etc.) to the
    // current carrier's `<C>.is_ring` instance.
    //
    // Prefers the abstract `Ring.<lemma>` from `Algebra.ring_lemmas`
    // applied with the carrier instance; falls back to the per-carrier
    // name when the abstract isn't in scope (e.g., Integer's
    // rep-level reflexivity proofs that are shorter than the abstract
    // derivation would compile to).
    //
    // `args` are the lemma-specific term arguments after the IsRing
    // instance (e.g., `x` for `zero_multiply(x)`, `a, b` for
    // `multiply_negate_left(a, b)`).
    // The seven leading arguments every abstract `Ring.<lemma>` over a
    // generic `IsRing` takes: (carrier, add, zero, negate, multiply, one,
    // isRing). The binary/unary operation values (add/negate/multiply)
    // are passed BARE — under a bundled ring their structure argument is
    // implicit and is recovered from the lemma's expected operation type
    // — while the nullary constants (zero/one) and the IsRing instance
    // carry the structure prefix (`Ring.zero(s)`, `Ring.is_ring(s)`). For
    // a concrete carrier the prefix is empty, so all seven are the plain
    // `<carrier>.*` constants, exactly as before.
    void appendIsRingInstanceArgs(
        ExpressionPointer& call,
        const RingNormalisationContext& context);

    ExpressionPointer buildAbstractRingLemmaApplication(
        const std::string& abstractLemmaName,
        const std::string& fallbackPerCarrierName,
        const std::string& fallbackHumanName,
        const std::vector<ExpressionPointer>& args,
        const RingNormalisationContext& context);

    // Build a proof of `zero * x = zero` (onLeft = true) or
    // `x * zero = zero` (onLeft = false) for the current carrier.
    ExpressionPointer buildRingAnnihilatorProof(
        bool onLeft,
        ExpressionPointer x,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // Build a proof of `(-a) * b = -(a * b)` (onLeft = true) or
    // `a * (-b) = -(a * b)` (onLeft = false).
    ExpressionPointer buildRingMultiplyNegateProof(
        bool onLeft,
        ExpressionPointer a, ExpressionPointer b,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    ExpressionPointer proveMultiplyMerge(
        const RingPolynomial& leftPoly,
        const RingPolynomial& rightPoly,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // Substitute every BoundVariable with the given index in `body` by
    // `argument`. Indices below the target are decreased by 1 only when
    // the substitution makes a position pass through a binder (we don't
    // walk through binders here — there are none in our motives, which
    // are flat applications + constants + the single bound variable
    // we're substituting).
    //
    // For our use we just need a shallow substitution: replace
    // BoundVariable(0) with `argument`, treating the body as a kernel
    // expression that doesn't introduce any further binders.

    // Rewrite the summand at position `position` in a flat left-
    // associated sum of `totalCount` summands. Caller supplies the
    // current form, the proof that the summand at that position equals
    // `newSummand`, and we construct the resulting form's expression
    // and the congruence proof.
    //
    // For position `position` in a left-associated sum:
    //   sum = ((((s_0 + s_1) + s_2) + ...) + s_{n-1})
    // To target s_k for rewriting, we build the motive
    //   λ z. ((((s_0 + ... + s_{k-1}) + z) + s_{k+1}) + ...) + s_{n-1}.
    ExpressionPointer rewriteFlatSummandAtPosition(
        ExpressionPointer currentForm,
        size_t position, size_t totalCount,
        ExpressionPointer replacement,
        const RingNormalisationContext& context);

    ExpressionPointer rewriteFlatSummandAtPositionProof(
        ExpressionPointer currentForm,
        size_t position, size_t totalCount,
        ExpressionPointer oldSummand,
        ExpressionPointer newSummand,
        ExpressionPointer summandProof,
        const RingNormalisationContext& context);

    // Prove `Li * Rj = targetMonomial` where Li, Rj are signed-monomial
    // kernels and targetMonomial = canonical kernel of (sign(Li)*sign(Rj),
    // sort(Li.sig ++ Rj.sig)).
    //
    // Steps (depending on signs):
    //   (++): Li * Rj = leftProduct * rightProduct. Flatten + sort the
    //         combined factors. The merged sign is +, so the canonical
    //         is just the product with no negate wrapper.
    //   (+-): Li * (-Mj) = -(Li * Mj). Use multiply_negate_right. Then
    //         the inner Li * Mj is the same as (++) case but with
    //         positive Mj. So: rewrite Rj → -Mj using nothing (it IS
    //         -Mj), apply multiply_negate_right, then recurse.
    //   (-+): symmetric, multiply_negate_left.
    //   (--): (-Mi) * (-Mj) = -(-Mi * Mj) = Mi * Mj. Both rules + negate_negate.
    //
    // After sign-pushing the outer negate, we have ±(product_of_factors).
    // The inner product is leftFactors * rightFactors with shapes:
    //   leftFactors  = leftProduct  (a left-assoc product of Li.sig atoms)
    //   rightFactors = rightProduct (left-assoc of Rj.sig atoms)
    // Concatenating: leftProduct * rightProduct. Re-associate to flat,
    // then sort to match mergedSig. Wrap in negate if mergedSign == -1.
    ExpressionPointer proveSignedProductEqualsMonomial(
        ExpressionPointer Li, ExpressionPointer Rj,
        const SignedMonomial& leftMono, const SignedMonomial& rightMono,
        const RingMonomialSignature& /*mergedSig*/, int mergedSign,
        ExpressionPointer targetMonomial,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // ----------------------------------------------------------------
    // proveNegateMerge: prove
    //   negate(canonical(innerPoly)) = canonical(-innerPoly)
    // ----------------------------------------------------------------
    //
    // Strategy:
    //   1. Push the outer negate through every `+` via negate_add.
    //   2. For each summand: if it was a positive monomial M, negate(M)
    //      is the canonical form of -M; if it was a negative monomial
    //      -M = negate(M), negate(negate(M)) collapses to M via
    //      negate_negate.
    //   3. Re-sort to match canonical(-innerPoly) (signatures are
    //      unchanged by sign flip, so the order is the same).
    //
    // Edge case: innerPoly empty → negate(zero). Derived from
    //   sym(addZeroRight(-0))   : -0 = -0 + 0
    //   addNegateLeft(0)        : -0 + 0 = 0
    //   trans                   : -0 = 0
    // (No primitive `negate_zero` axiom is required.)
    ExpressionPointer proveNegateMerge(
        const RingPolynomial& innerPoly,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // =====================================================================
    // Mod-(2^64 - 59) value fingerprint
    //
    // Diagnostic used by `ring` / `field` when symbolic decision fails:
    // evaluate both sides as elements of GF(p) for p = 2^64 - 59, with
    // each "opaque atom" replaced by its 64-bit subtree hash. If the
    // values disagree, the identity is (with overwhelming probability)
    // not a polynomial / field identity at all — the user's math is
    // wrong, not the tactic's. If the values agree, the goal is almost
    // certainly true and the symbolic failure points at a tactic
    // limitation (or a missing hypothesis).
    //
    // False-positive rate (agreeing on an unequal identity) is bounded
    // by Schwartz-Zippel: roughly `degree / p`, well under 2^-50 for
    // any sensible goal. False negatives (disagreeing on an equal
    // identity) require a 64-bit hash collision and are equally rare.
    //
    // Division by zero in the evaluator (a denominator's fingerprint
    // happens to be 0) returns nullopt and we say so clearly rather
    // than misleading the user with a false claim.
    // =====================================================================

    static constexpr uint64_t kFingerprintModulus =
        18446744073709551557ull;  // 2^64 - 59 (prime)

    // GF(2^64 - 59) fingerprint arithmetic + evaluator + diagnostic.
    // Defined out-of-line in elaborator_ring.cpp.
    uint64_t fingerprintAdd(uint64_t leftValue, uint64_t rightValue) const;
    uint64_t fingerprintSubtract(
        uint64_t leftValue, uint64_t rightValue) const;
    uint64_t fingerprintNegate(uint64_t value) const;
    uint64_t fingerprintMultiply(
        uint64_t leftValue, uint64_t rightValue) const;
    uint64_t fingerprintModularPower(
        uint64_t base, uint64_t exponent) const;
    std::optional<uint64_t> fingerprintModularInverse(uint64_t value) const;
    std::optional<uint64_t> evaluateFingerprint(
        ExpressionPointer expression,
        const std::string& carrierName) const;
    std::string buildFingerprintDiagnostic(
        ExpressionPointer leftEndpoint,
        ExpressionPointer rightEndpoint,
        const std::string& carrierName) const;

    // v2 of the ring tactic. Called as a fallback when v1 (pure-AC)
    // can't close the goal. Returns the proof on success; throws
    // otherwise. `expectedType` is the equality goal.
    ExpressionPointer elaborateRingByNormalisation(
        const std::vector<LocalBinder>& /*localBinders*/,
        ExpressionPointer leftEndpoint,
        ExpressionPointer rightEndpoint,
        ExpressionPointer carrierType,
        LevelPointer carrierUniverseLevel,
        const std::string& carrierName,
        int line);

    // =====================================================================
    // `field(h1, h2, ...)` — extends the ring normaliser with the side relation
    // `t_i * reciprocal_function(t_i) = 1` for each user-supplied
    // hypothesis `h_i : ¬(t_i = Rational.zero)`.
    //
    // Strategy: normalise both sides via the ring normaliser treating
    // `reciprocal_function(t_i)` and `t_i` as opaque atoms. In each
    // monomial of the canonical polynomial, count matched (t_i, r_i)
    // pairs and contract them (each contraction drops one t_i and one
    // r_i from the monomial's factor signature). After contraction the
    // polynomials of both sides should agree; if not, the goal is not a
    // field identity (or the user supplied insufficient hypotheses).
    //
    // The proof is built as a five-segment chain:
    //
    //   LHS = ring_canonical(LHS)
    //       = field_canonical(LHS)         -- via per-monomial contraction
    //       = field_canonical(RHS)         -- reflexivity (literally equal)
    //       = ring_canonical(RHS)          -- symmetric of contraction
    //       = RHS
    //
    // Each per-monomial contraction proof rearranges the monomial's
    // factor list via the single-operator AC sorter, then applies
    // `reciprocal_function_multiplies` plus `multiply_one` to remove
    // each (t_i, r_i) pair from the tail.
    // =====================================================================

    // A registered (t_i, r_i) pair from the user's nonzero hypotheses.
    struct FieldReciprocalPair {
        ExpressionPointer baseAtom;        // t_i kernel expression
        ExpressionPointer reciprocalAtom;  // reciprocal_function(t_i)
        ExpressionPointer multipliesProof; // proof : t_i * reciprocal_function(t_i) = 1
        uint64_t baseHash;
        uint64_t reciprocalHash;
    };

    // Contract a sorted monomial signature using the supplied pairs.
    // Returns the new signature with up to `min(#t, #r)` of each pair
    // removed. Side-effect: writes the number of pairs cancelled per
    // pair index into `pairsRemovedOut`.
    RingMonomialSignature contractMonomialSignature(
        const RingMonomialSignature& signature,
        const std::vector<FieldReciprocalPair>& pairs,
        std::vector<int>& pairsRemovedOut);

    // Build a polynomial from a `ring_canonical_polynomial` by applying
    // contractions monomial-by-monomial. Aggregates like terms (same
    // signature) by summing coefficients. Out-of-band: the per-monomial
    // contraction record (signature → list-of-pair-removals) is filled
    // in `contractionRecords` for the proof emitter.
    struct FieldMonomialContraction {
        RingMonomialSignature originalSignature;
        int originalCoefficient;
        RingMonomialSignature contractedSignature;
        std::vector<int> pairsRemoved;  // by pair index
    };
    RingPolynomial buildContractedPolynomial(
        const RingPolynomial& original,
        const std::vector<FieldReciprocalPair>& pairs,
        std::vector<FieldMonomialContraction>& contractionRecords);

    // Build a proof
    //   (factor_0 * ... * factor_{n-1})
    //     = (factor'_0 * ... * factor'_{n-k-1})
    // where the right side is the left side with the indicated
    // (baseAtom, reciprocalAtom) pairs removed.  `factorList` is the
    // monomial's full factor list (in canonical order, repeated per
    // multiplicity).  `pairs` is the registry; `pairsRemoved[i]`
    // indicates how many copies of pair i should be removed.
    //
    // Strategy:
    //   1. Compute the surviving factor list by removing pair members
    //      from the back to front (this matches the canonical iteration
    //      order, which is hash-sorted).
    //   2. Build the "rearranged" factor list = survivingFactors ++
    //      [t_1, r_1, t_1, r_1, ...] (one (t, r) pair per cancellation).
    //   3. Prove `factorList-product = rearranged-product` via
    //      `proveProductEqualsSorted` (single-operator AC sorter, ANY permutation).
    //   4. Cancel pairs from the tail: each step uses
    //        ((prefix * t) * r) = prefix * (t * r)     (multiply_associative)
    //        prefix * (t * r) = prefix * 1             (congr + multiplies_proof)
    //        prefix * 1 = prefix                       (multiply_one)
    //   5. Repeat until all pairs are cancelled.
    //
    // Returns the proof.  Requires factorList.size() > 0.
    ExpressionPointer buildFactorContractionProof(
        const std::vector<ExpressionPointer>& factorList,
        const std::vector<FieldReciprocalPair>& pairs,
        const std::vector<int>& pairsRemoved,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // Build kernel proof of `monomialCanonicalKernel = contractedCanonicalKernel`,
    // where `monomialCanonicalKernel` is the canonical form of an
    // original monomial (signature, coefficient) and
    // `contractedCanonicalKernel` is the canonical form of the
    // contracted monomial (after removing the indicated pairs).
    // The two coefficients must be equal in magnitude (no like-term
    // collisions at the per-monomial level — those are handled by the
    // caller).
    //
    // The proof is built on the factor-product level (without the
    // outer sign-wrap) and then lifted through the negate (if the
    // coefficient is -1) via congruence.
    ExpressionPointer buildMonomialContractionProof(
        const RingMonomialSignature& originalSignature,
        int coefficient,
        const RingMonomialSignature& contractedSignature,
        const std::vector<int>& pairsRemoved,
        const std::vector<FieldReciprocalPair>& pairs,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // Build kernel proof of `canonical(P) = canonical(P_contracted)`
    // where P_contracted is the polynomial obtained from P by
    // contracting each monomial individually.  This assumes no
    // collisions: each contracted monomial has a unique signature in
    // P_contracted, and coefficients are unchanged. The proof works
    // by walking the canonical sum left-to-right and applying
    // per-monomial congruences.
    ExpressionPointer buildPolynomialContractionProof(
        const RingPolynomial& originalPoly,
        const RingPolynomial& contractedPoly,
        const std::vector<FieldMonomialContraction>& contractionRecords,
        const std::vector<FieldReciprocalPair>& pairs,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames);

    // Walk a kernel expression and accumulate every `reciprocal_function`
    // application's argument into `argumentsOut` (deduplicating by hash).
    void collectReciprocalArguments(
        ExpressionPointer expression,
        const std::string& reciprocalFunctionName,
        std::unordered_map<uint64_t, ExpressionPointer>& argumentsOut);

    // `field(h1, h2, ..., hn)` — closes a Rational (or any field with a
    // `reciprocal_function`) equality using `ring` plus the
    // `reciprocal_function_multiplies` law and the user-supplied
    // nonzero hypotheses.
    ExpressionPointer elaborateField(
        const SurfaceField& fieldTactic,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    // `sorry` — desugars to either `Internal.sorry_proposition(<P>)`
    // (when the expected type is a Proposition, i.e. lives in `Sort 0`)
    // or `Internal.sorry.{u}(<T>)` (when the expected type lives in
    // `Type(u) = Sort (u+1)` for some u). Either way emits a warning at
    // the use site so the gap is visible in the build log.
    ExpressionPointer elaborateSorry(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "sorry placeholder at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "`sorry` needs an expected type from context — wrap "
                "with an ascription `(sorry : T)` or supply one via "
                "context");
        }
        // Determine: is the expected type a Proposition (`Sort 0`) or
        // a Type-universe value (`Sort (u+1)` for some u ≥ 0)?
        bool isProposition = false;
        LevelPointer universeLevel;
        try {
            Context openedContext = buildContextFromLocalBinders(localBinders);
            ExpressionPointer expectedTypeOpened = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            ExpressionPointer typeOfType = inferType(
                environment_, openedContext, expectedTypeOpened);
            ExpressionPointer typeOfTypeReduced = weakHeadNormalForm(
                environment_, typeOfType);
            auto* sortNode = std::get_if<Sort>(&typeOfTypeReduced->node);
            if (!sortNode) {
                throwElaborate(
                    "`sorry` cannot determine the universe of the "
                    "expected type — its type is not a Sort");
            }
            LevelPointer sortLevel = sortNode->level;
            if (auto* successor =
                    std::get_if<LevelSuccessor>(&sortLevel->node)) {
                universeLevel = successor->base;
            } else if (auto* constant =
                            std::get_if<LevelConst>(&sortLevel->node)) {
                if (constant->value == 0) {
                    isProposition = true;
                } else {
                    universeLevel = makeLevelConst(constant->value - 1);
                }
            } else {
                throwElaborate(
                    "`sorry`: expected type's universe is neither "
                    "`Proposition` nor `Type(u)` for a known u");
            }
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        std::string axiomName = isProposition
            ? "Internal.sorry_proposition"
            : "Internal.sorry";
        if (environment_.lookup(axiomName) == nullptr) {
            throwElaborate(
                "`sorry` requires `" + axiomName + "` in scope "
                "(import axioms)");
        }
        std::cerr << "warning: `sorry` used"
                  << (currentDeclarationName_.empty()
                          ? ""
                          : (" in '" + currentDeclarationName_ + "'"))
                  << " at line " << line << "\n";
        ExpressionPointer call;
        if (isProposition) {
            call = makeConstant(axiomName);
        } else {
            call = makeConstant(axiomName, {universeLevel});
        }
        call = makeApplication(std::move(call), expectedType);
        return call;
    }

    // `⟨a, b, ..., n⟩` at expected type `I(...)`: desugars to a call of
    // I's unique constructor. When the constructor takes more value-args
    // than there are tuple components, the user's tuple is under-sized
    // and we error. When the constructor takes exactly N value-args, we
    // emit a direct constructor application. When the constructor takes
    // K < N value-args and K == 2, we right-associate: `⟨a, b, c⟩` at
    // `Exists(_, _)` becomes `Exists.introduce(a, ⟨b, c⟩)` and the inner
    // `⟨b, c⟩` is elaborated against the second-argument's expected
    // type. (This is the conventional shape for nested Exists/And.)
    ExpressionPointer elaborateAnonymousTuple(
        const SurfaceAnonymousTuple& tuple,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {

        if (!expectedType) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' needs an expected type from "
                "context (line " + std::to_string(line) + ")");
        }
        // Force opaque heads transparent so an `IsNonneg(x)`-typed expected
        // type exposes its underlying `Exists` inductive — the construct-site
        // counterpart of the kernel's opacity-tolerant retries (replaces the
        // old `unfold IsNonneg in ⟨…⟩` wrap).
        ExpressionPointer head =
            weakHeadNormalFormForcingOpaqueHead(expectedType);
        ExpressionPointer headFunction = head;
        while (auto* application =
                   std::get_if<Application>(&headFunction->node)) {
            headFunction = application->function;
        }
        auto* constant = std::get_if<Constant>(&headFunction->node);
        if (!constant) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line)
                + ": expected type does not have an inductive head");
        }
        const Declaration* inductiveDecl =
            environment_.lookup(constant->name);
        auto* inductive = inductiveDecl
            ? std::get_if<Inductive>(inductiveDecl) : nullptr;
        if (!inductive) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line)
                + ": expected type's head '" + constant->name
                + "' is not an inductive");
        }
        if (inductive->constructorNames.size() != 1) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line)
                + ": expected single-constructor inductive, but '"
                + constant->name + "' has "
                + std::to_string(inductive->constructorNames.size())
                + " constructors");
        }
        const std::string& constructorName =
            inductive->constructorNames[0];
        const Declaration* constructorDecl =
            environment_.lookup(constructorName);
        auto* constructor = constructorDecl
            ? std::get_if<Constructor>(constructorDecl) : nullptr;
        if (!constructor) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line)
                + ": constructor '" + constructorName
                + "' missing from environment");
        }
        int totalPiCount = countLeadingPis(constructor->type);
        int valueArgumentCount =
            totalPiCount - inductive->numParameters;
        size_t componentCount = tuple.components.size();
        if (componentCount == 0) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' is empty at line "
                + std::to_string(line));
        }
        // Build a SurfaceApplication and re-elaborate it so that the
        // existing constructor parameter inference path handles it.
        std::vector<SurfaceExpressionPointer> components;
        if (static_cast<int>(componentCount) == valueArgumentCount) {
            components = tuple.components;
        } else if (valueArgumentCount == 2 && componentCount > 2) {
            components.push_back(tuple.components[0]);
            std::vector<SurfaceExpressionPointer> tail(
                tuple.components.begin() + 1, tuple.components.end());
            components.push_back(makeSurfaceAnonymousTuple(
                std::move(tail), line, column));
        } else {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line) + ": constructor '"
                + constructorName + "' takes "
                + std::to_string(valueArgumentCount)
                + " value argument(s), got "
                + std::to_string(componentCount)
                + " tuple component(s)");
        }
        SurfaceExpressionPointer constructorReference =
            makeSurfaceIdentifier(constructorName, {}, line, column);
        SurfaceExpressionPointer surfaceCall = makeSurfaceApplication(
            std::move(constructorReference), std::move(components),
            line, column);
        // Pass the inductive-headed `head` (opaque wrappers forced off) as the
        // expected type, NOT the original opaque `expectedType` — the
        // constructor-parameter inference needs to read the inductive's
        // arguments (e.g. `Exists`'s predicate) from it. The kernel's defeq
        // bridge re-checks the built term against the opaque expected type.
        return elaborateExpression(*surfaceCall, localBinders, head);
    }

    // Handle a `cases` / `obtain` expression whose scrutinee is a
    // `Quotient.{u}(T, R)` value. Quotient is an axiomatic primitive,
    // not an inductive, so the standard recursor path doesn't apply.
    // We build a `Quotient.induct.{u}(T, R, motive, λ rep ⇒ body,
    // scrutinee)` term directly.
    //
    // Restrictions: exactly one clause; pattern shape
    // `Quotient.mk(rep)` with a single bare-name argument; scrutinee is
    // a local-binder variable (so we can abstract it from the goal).
    // Expected type must reduce to a Proposition since `Quotient.induct`
    // requires a Proposition-valued motive.
    ExpressionPointer elaborateQuotientCases(
        const SurfaceCases& cases,
        ExpressionPointer scrutinee,
        ExpressionPointer scrutineeTypeOpened,
        const std::vector<ExpressionPointer>& inductiveArguments,
        const Constant& quotientConstant,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "quotient-cases at line " + std::to_string(line));

        // Verify scrutinee is a local-binder variable so we can
        // abstract it from the goal.
        auto* scrutineeBoundVariable =
            std::get_if<BoundVariable>(&scrutinee->node);
        if (!scrutineeBoundVariable
            || scrutineeBoundVariable->deBruijnIndex < 0
            || scrutineeBoundVariable->deBruijnIndex
                   >= static_cast<int>(localBinders.size())) {
            throwElaborate(
                "quotient-cases scrutinee must be a local-binder "
                "variable (a parameter or let-binding name)");
        }
        int scrutineeDeBruijn = scrutineeBoundVariable->deBruijnIndex;

        // Quotient takes 2 args: T and R. The kernel's universe-arg
        // count is always 1 for Quotient.
        if (inductiveArguments.size() != 2) {
            throwElaborate(
                "internal: Quotient applied to "
                + std::to_string(inductiveArguments.size())
                + " arguments, expected 2 (T, R)");
        }
        if (quotientConstant.universeArguments.size() != 1) {
            throwElaborate(
                "internal: Quotient should have exactly one universe "
                "argument");
        }
        LevelPointer quotientUniverse =
            quotientConstant.universeArguments[0];
        ExpressionPointer carrierTypeOpened = inductiveArguments[0];
        ExpressionPointer relationOpened = inductiveArguments[1];
        ExpressionPointer carrierType = closeOverLocalBinders(
            carrierTypeOpened, localBinders, localBinders.size());
        ExpressionPointer relation = closeOverLocalBinders(
            relationOpened, localBinders, localBinders.size());
        ExpressionPointer scrutineeType = closeOverLocalBinders(
            scrutineeTypeOpened, localBinders, localBinders.size());

        if (cases.clauses.size() != 1) {
            throwElaborate(
                "quotient-cases takes exactly one clause "
                "(`<rep> => …` or `Quotient.mk(<rep>) => …`), got "
                + std::to_string(cases.clauses.size()));
        }
        const SurfaceCasesClause& clause = cases.clauses[0];

        // Accepted pattern shapes (where <pat_inner> is itself a bare
        // name or a constructor pattern over the carrier type):
        //   - <bare_name>                      — bind rep, no destructure
        //   - Quotient.mk(<pat_inner>)         — explicit wrap (legacy)
        //   - <Constructor.…>(args)            — destructure rep directly
        //
        // For the non-bare-name inner patterns, we synthesise a fresh
        // representative binder name and wrap the user's body in
        // `cases <fresh> { | <pat_inner> => <body> }` so the underlying
        // structural-recursor elaboration handles the destructure.
        std::string representativeName;
        SurfacePatternPointer innerDestructurePattern;  // non-null iff
                                                         // we need to
                                                         // wrap the body
        {
            auto* bareName = std::get_if<SurfacePatternBareName>(
                &clause.pattern->node);
            auto* constructorPattern =
                std::get_if<SurfacePatternConstructor>(&clause.pattern->node);
            if (bareName) {
                // `cases x { | rep_x => body }`: no destructure.
                representativeName = bareName->name;
            } else if (constructorPattern
                && constructorPattern->constructorName == "Quotient.mk") {
                if (constructorPattern->arguments.size() != 1) {
                    throwElaborate(
                        "quotient-cases: `Quotient.mk` pattern takes "
                        "one argument (the representative), got "
                        + std::to_string(
                            constructorPattern->arguments.size()));
                }
                auto* innerBareName = std::get_if<SurfacePatternBareName>(
                    &constructorPattern->arguments[0]->node);
                if (innerBareName) {
                    representativeName = innerBareName->name;
                } else {
                    representativeName = "_quotientRep_"
                        + std::to_string(clause.line) + "_"
                        + std::to_string(clause.column);
                    innerDestructurePattern =
                        constructorPattern->arguments[0];
                }
            } else if (constructorPattern) {
                // `cases x { | <Constructor>(args) => body }` —
                // destructure directly. Synthesise the rep binder.
                representativeName = "_quotientRep_"
                    + std::to_string(clause.line) + "_"
                    + std::to_string(clause.column);
                innerDestructurePattern = clause.pattern;
            } else if (std::get_if<SurfacePatternTuple>(
                           &clause.pattern->node)) {
                // `cases x { | ⟨a, b⟩ => body }` — destructure the
                // representative via the carrier's sole constructor
                // (resolved by the inner cases from the carrier type, so
                // the constructor name need not be written). This is the
                // form `by_representatives x as ⟨a, b⟩` desugars to.
                representativeName = "_quotientRep_"
                    + std::to_string(clause.line) + "_"
                    + std::to_string(clause.column);
                innerDestructurePattern = clause.pattern;
            } else {
                throwElaborate(
                    "quotient-cases pattern must be a bare name "
                    "(binding the representative), a constructor "
                    "pattern or tuple `⟨…⟩` over the carrier type "
                    "(destructures the representative), or "
                    "`Quotient.mk(<inner>)`");
            }
        }

        // Build the motive: `λ q : Quotient.{u}(T, R) ⇒
        // expectedType[scrutinee := q]`. We abstract the scrutinee's
        // local index out of expectedType; the resulting body's
        // BoundVariable(0) refers to the new motive binder.
        ExpressionPointer motiveBody =
            abstractOverBoundVariables(expectedType, {scrutineeDeBruijn});
        ExpressionPointer motive = makeLambda(
            "_quotient_target", scrutineeType, motiveBody);

        // Set up the inner local-binder context with the representative
        // binder on top.
        std::vector<LocalBinder> innerBinders = localBinders;
        innerBinders.push_back({representativeName, carrierType});

        // Build the body's expected type as `motive(Quotient.mk(T, R, rep))`
        // in inner context. Shift outer terms up by 1 to account for the
        // new binder; rep is BoundVariable(0). The kernel's WHNF will
        // beta-reduce when needed.
        ExpressionPointer carrierTypeInner = shift(carrierType, 1);
        ExpressionPointer relationInner = shift(relation, 1);
        ExpressionPointer motiveInner = shift(motive, 1);
        ExpressionPointer mkAppliedToRep =
            makeApplication(
                makeApplication(
                    makeApplication(
                        makeConstant("Quotient.mk", {quotientUniverse}),
                        carrierTypeInner),
                    relationInner),
                makeBoundVariable(0));
        ExpressionPointer bodyExpectedType =
            makeApplication(motiveInner, mkAppliedToRep);

        // If the user supplied a destructure pattern on the rep,
        // synthesize a `cases <fresh_rep> { | <inner_pattern> => <body> }`
        // wrap before elaborating; otherwise elaborate the body directly.
        SurfaceExpressionPointer bodySurface = clause.body;
        if (innerDestructurePattern) {
            SurfaceExpressionPointer scrutineeIdentifier =
                makeSurfaceIdentifier(representativeName, {},
                                       clause.line, clause.column);
            SurfaceCasesClause innerClause;
            innerClause.pattern = innerDestructurePattern;
            innerClause.body = bodySurface;
            innerClause.line = clause.line;
            innerClause.column = clause.column;
            std::vector<SurfaceCasesClause> innerClauses;
            innerClauses.push_back(std::move(innerClause));
            bodySurface = makeSurfaceCases(
                std::move(scrutineeIdentifier),
                std::move(innerClauses),
                clause.line, clause.column);
        }

        // Elaborate the body in the extended local context.
        ExpressionPointer bodyKernel =
            elaborateExpression(*bodySurface, innerBinders,
                                 bodyExpectedType);
        // Run the diff/class-equality coercions on the body, exactly as the
        // structural-`cases` and lambda-body paths do. Without this a
        // quotient-`cases` arm whose body proves the bare equivalence
        // `R(g x, g y)` could not close a `motive(mk rep)` goal that
        // reduces to `mk(g x) = mk(g y)` (e.g. the outer respect of a
        // binary define-by-representatives, whose goal is a literal
        // `Quotient.lift(…, mk rep)` equality).
        // WHNF the expected type first: it is the motive *applied* to
        // `mk(rep)` (an unreduced redex), and coerceToExpectedTypeViaDiff's
        // cheap prefilter checks for an `Equality` head without reducing —
        // so the beta-redex would hide the goal and the coercion would bail.
        bodyKernel = coerceToExpectedTypeViaDiff(
            innerBinders, bodyKernel,
            weakHeadNormalForm(environment_, bodyExpectedType));

        // Wrap the body in the representative-case lambda.
        ExpressionPointer representativeCaseLambda = makeLambda(
            representativeName, carrierType, bodyKernel);

        // Final application: Quotient.induct(T, R, motive,
        //                                     λ rep ⇒ body, scrutinee).
        ExpressionPointer quotientInductHead =
            makeConstant("Quotient.induct", {quotientUniverse});
        return makeApplication(
            makeApplication(
                makeApplication(
                    makeApplication(
                        makeApplication(quotientInductHead, carrierType),
                        relation),
                    motive),
                representativeCaseLambda),
            scrutinee);
    }

    // Render a `SurfacePattern` back into a `SurfaceExpression` for
    // use as the right-hand side of the per-arm equation in the
    // `cases X with equalityHypothesisName { … }` desugaring.
    // Constructor patterns become applications of the constructor's
    // name to the bound argument names. Tuple patterns are
    // disallowed (the convoy doesn't add information on
    // single-constructor inductives, and the rest of the desugar
    // would have to re-route through the tuple's lone constructor —
    // not worth the complexity for the v1 cut).
    SurfaceExpressionPointer patternToSurfaceExpression(
        SurfacePatternPointer pattern) {
        int line = pattern->line;
        int column = pattern->column;
        if (auto* bare =
                std::get_if<SurfacePatternBareName>(&pattern->node)) {
            return makeSurfaceIdentifier(bare->name, {},
                                          line, column);
        }
        if (auto* constructorPattern =
                std::get_if<SurfacePatternConstructor>(&pattern->node)) {
            SurfaceExpressionPointer head = makeSurfaceIdentifier(
                constructorPattern->constructorName, {}, line, column);
            if (constructorPattern->arguments.empty()) {
                return head;
            }
            std::vector<SurfaceArgument> arguments;
            for (const auto& argumentPattern :
                     constructorPattern->arguments) {
                SurfaceArgument argument;
                argument.value =
                    patternToSurfaceExpression(argumentPattern);
                arguments.push_back(std::move(argument));
            }
            return makeSurfaceApplication(std::move(head),
                                           std::move(arguments),
                                           line, column);
        }
        throwElaborate(
            "cases ... with equalityHypothesis: tuple patterns are "
            "not yet supported in the convoy desugaring; the "
            "`function`+`cases` form still works as a fallback");
        return nullptr;  // unreachable
    }

    // `cases X with equalityHypothesisName { … }` — the "convoy" form.
    //
    // Each arm gets an extra binder
    //   `equalityHypothesisName : X = <constructor pattern>`
    // in scope. Implements the user's explicit
    //   `(function (caseScrutineeVariable : T)
    //              (equalityHypothesisOuter : X = caseScrutineeVariable) =>
    //      (cases caseScrutineeVariable {
    //         | ctor(args) => function (equalityHypothesisName : X = ctor(args)) => body
    //       } : (… : X = caseScrutineeVariable) → Goal)(
    //          equalityHypothesisOuter))
    //   (X)(reflexivity(X))`
    // pattern, but without the user having to write any of it.
    //
    // Kernel-level details:
    //   - The user's expected type `Goal` is passed in CLOSED form
    //     (BoundVariable indices relative to the surrounding theorem
    //     binders). We extend localBinders with the two new convoy
    //     binders and lift Goal accordingly when we drop it into the
    //     inner Pi.
    //   - The "constructor pattern as surface expression" is
    //     reconstructed from each clause's pattern; the names that
    //     bind constructor arguments inside the pattern reappear as
    //     references in the equation type, so the elaborator wires
    //     them up by name during the inner case-arm elaboration.
    //   - The inner cases is elaborated against an expected type of
    //     `(_inner : X = caseScrutineeVariable) → Goal`. The standard
    //     `elaborateCasesExpression` motive-inference picks the
    //     scrutinee-abstracted motive `λ s. (… : X = s) → Goal` from
    //     this; each arm then has expected type
    //     `(… : X = <constructor pattern>) → Goal`, which is exactly
    //     the surface lambda we wrapped around the user's body.
    ExpressionPointer elaborateCasesWithEqualityHypothesis(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "cases ... with " + cases.equalityHypothesisName
            + " at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "cases X with " + cases.equalityHypothesisName
                + " { … } needs an expected type from context");
        }
        // (1) Elaborate the scrutinee X. Get T (closed) and its
        // universe level.
        ExpressionPointer scrutineeKernel = elaborateExpression(
            *cases.scrutinee, localBinders);
        ExpressionPointer scrutineeTypeOpened = weakHeadNormalForm(
            environment_,
            inferTypeInLocalContext(localBinders, scrutineeKernel));
        ExpressionPointer scrutineeType = closeOverLocalBinders(
            scrutineeTypeOpened, localBinders, localBinders.size());
        LevelPointer scrutineeUniverse =
            typeUniverseOf(localBinders, scrutineeKernel);

        // (2) Names for the two convoy binders. The internal "_" prefix
        // avoids any chance of colliding with user-visible names; the
        // user only ever sees `equalityHypothesisName` (theirs).
        const std::string caseScrutineeName =
            "_caseScrutineeFor_" + cases.equalityHypothesisName;
        const std::string outerEqualityName =
            "_equalityHypothesisOuterFor_"
            + cases.equalityHypothesisName;

        // (3) Build the equality-type for the OUTER binder in extended
        // scope. After adding `caseScrutineeName : T` to localBinders,
        // BoundVariable(0) refers to that binder, and references to the
        // original local binders shift up by 1.
        ExpressionPointer scrutineeTypeLiftedOnce =
            liftBoundVariables(scrutineeType, 1, 0);
        ExpressionPointer scrutineeKernelLiftedOnce =
            liftBoundVariables(scrutineeKernel, 1, 0);
        ExpressionPointer outerEqualityType = makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality", {scrutineeUniverse}),
                    scrutineeTypeLiftedOnce),
                scrutineeKernelLiftedOnce),
            makeBoundVariable(0));

        std::vector<LocalBinder> extendedLocalBinders = localBinders;
        extendedLocalBinders.push_back(
            {caseScrutineeName, scrutineeType});
        extendedLocalBinders.push_back(
            {outerEqualityName, outerEqualityType});

        // (4) Construct the synthetic `SurfaceCases` whose scrutinee is
        // the new binder `caseScrutineeName` and whose arm bodies are
        // wrapped in
        //   function (equalityHypothesisName : X = <ctor pattern>) =>
        //     <original body>
        // so the equation binder is visible inside the user's body
        // while the rest of the surface elaboration runs unchanged.
        std::vector<SurfaceCasesClause> wrappedClauses;
        for (const auto& clause : cases.clauses) {
            SurfaceCasesClause wrappedClause;
            wrappedClause.pattern = clause.pattern;
            wrappedClause.line = clause.line;
            wrappedClause.column = clause.column;
            SurfaceExpressionPointer patternExpression =
                patternToSurfaceExpression(clause.pattern);
            // `cases.scrutinee = patternExpression` via the surface
            // binary-operator builder; the existing elaborator path
            // turns this into `Equality.{…}(T, X, ctorPattern)`.
            SurfaceExpressionPointer equationType =
                makeSurfaceBinaryOperation(
                    "=", cases.scrutinee, patternExpression,
                    clause.line, clause.column);
            SurfaceBinder equationBinder;
            equationBinder.names = {cases.equalityHypothesisName};
            equationBinder.type = equationType;
            equationBinder.isImplicit = false;
            wrappedClause.body = makeSurfaceLambda(
                std::move(equationBinder), clause.body,
                clause.line, clause.column);
            wrappedClauses.push_back(std::move(wrappedClause));
        }
        SurfaceExpressionPointer innerScrutinee = makeSurfaceIdentifier(
            caseScrutineeName, {}, line, column);
        SurfaceExpressionPointer syntheticCasesSurface =
            makeSurfaceCases(std::move(innerScrutinee),
                              std::move(wrappedClauses), line, column);

        // (5) Expected type for the inner cases, expressed in the
        // *extended* scope: `(eqInner : X = caseScrutineeVariable) → Goal`.
        // In closed form at extended depth: X lifted by 2, the
        // BoundVariable(1) reference to caseScrutineeVariable (depth + 2
        // means BV(0) is outerEqualityName, BV(1) is caseScrutineeName).
        ExpressionPointer scrutineeTypeLiftedTwice =
            liftBoundVariables(scrutineeType, 2, 0);
        ExpressionPointer scrutineeKernelLiftedTwice =
            liftBoundVariables(scrutineeKernel, 2, 0);
        ExpressionPointer innerEqualityType = makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality", {scrutineeUniverse}),
                    scrutineeTypeLiftedTwice),
                scrutineeKernelLiftedTwice),
            makeBoundVariable(1));
        // The Pi codomain lives one binder deeper than the extended
        // scope (i.e. orig + 3 binders total). Goal was closed at
        // orig, so lift by 3.
        ExpressionPointer goalLiftedByThree =
            liftBoundVariables(expectedType, 3, 0);
        ExpressionPointer innerExpectedType = makePi(
            "_innerEqualityHypothesisUnused",
            innerEqualityType, goalLiftedByThree);

        // (6) Elaborate the synthetic cases at the extended scope.
        ExpressionPointer innerCasesKernel = elaborateExpression(
            *syntheticCasesSurface, extendedLocalBinders,
            innerExpectedType);

        // (7) Apply the inner cases to outerEquality (BoundVariable(0)
        // at extended scope). The result has type `Goal` lifted by 2.
        ExpressionPointer appliedToOuter = makeApplication(
            innerCasesKernel, makeBoundVariable(0));

        // (8) Wrap in the two outer Lambdas (closing the convoy
        // binders).
        ExpressionPointer wrappedOuterEquality = makeLambda(
            outerEqualityName, outerEqualityType, appliedToOuter);
        ExpressionPointer wrappedCaseScrutinee = makeLambda(
            caseScrutineeName, scrutineeType, wrappedOuterEquality);

        // (9) Apply to (X, reflexivity(T, X)). reflexivity types as
        // `X = X`; the kernel reduces the outer Lambda's β to align
        // it with the Pi domain `X = caseScrutineeVariable`.
        ExpressionPointer reflexivityCall = makeApplication(
            makeApplication(
                makeConstant("reflexivity", {scrutineeUniverse}),
                scrutineeType),
            scrutineeKernel);
        ExpressionPointer fullyApplied = makeApplication(
            makeApplication(wrappedCaseScrutinee, scrutineeKernel),
            reflexivityCall);
        return fullyApplied;
        (void)column;
    }

    // `cases X refining h_1, …, h_N { case ctor: body … }` — the
    // "F1" sugar that automates the convoy pattern for binders whose
    // types mention the scrutinee.
    //
    // Desugars to:
    //
    //   (cases X {
    //      case ctor(args): function (h_1) (h_2) … (h_N) => body
    //      …
    //    } : (h_1 : T_h_1) → (h_2 : T_h_2) → … → (h_N : T_h_N) → Goal
    //   )(h_1, h_2, …, h_N)
    //
    // The inner-cases motive is `λ x. (h_1 : T_h_1(x)) → … → Goal(x)`,
    // so each arm's body has type `(h_1 : T_h_1(ctor(args))) → … →
    // Goal(ctor(args))` — the lambdas pick up the refined hypothesis
    // types via motive specialisation, no explicit annotation needed.
    // Outer application closes the chain by feeding the original
    // (unrefined-named-but-now-refined-at-this-case) binders back in.
    ExpressionPointer elaborateCasesWithRefining(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        if (!expectedType) {
            throwElaborate(
                "cases ... refining ... { ... } needs an expected "
                "type from context");
        }
        Frame frame(*this,
            "cases ... refining ... at line " + std::to_string(line));

        // (1) Resolve each refining name to its position in
        // localBinders (BoundVariable index from innermost) and its
        // type at depth localBinders.size() (lift from the depth at
        // which the binder was declared).
        int refiningCount = static_cast<int>(cases.refiningNames.size());
        std::vector<int> refiningBoundVariableIndices;
        std::vector<ExpressionPointer> refiningTypesAtOuterDepth;
        int totalBinders = static_cast<int>(localBinders.size());
        for (const auto& name : cases.refiningNames) {
            int positionInArray = -1;
            for (int i = totalBinders - 1; i >= 0; --i) {
                if (localBinders[i].name == name) {
                    positionInArray = i;
                    break;
                }
            }
            if (positionInArray < 0) {
                throwElaborate(
                    "cases ... refining " + name + ": no binder named '"
                    + name + "' is in scope");
            }
            refiningBoundVariableIndices.push_back(
                totalBinders - 1 - positionInArray);
            int liftAmount = totalBinders - positionInArray;
            refiningTypesAtOuterDepth.push_back(
                liftBoundVariables(
                    localBinders[positionInArray].type,
                    liftAmount, 0));
        }

        // (2) Build the wrapped expected type at the outer depth:
        //   Π (h_1 : T_1) Π (h_2 : T_2') … Π (h_N : T_N') Goal'
        // where each T_i' has references to h_1, …, h_{i-1} replaced
        // by the corresponding Π binder (and Goal' has all of h_1…h_N
        // replaced). This is the "generalize" / "revert" telescope
        // construction: we abstract one refining binder at a time,
        // starting from the innermost (h_N) and working outward.
        //
        // For each step, abstractOverBoundVariable shifts every OTHER
        // outer BV up by 1 to make room for the new Π's binder at
        // BV(0). So after `k` iterations, an outer BV originally at
        // index `j` (and not yet abstracted) lives at `j + k`. The
        // domain of the Π we're constructing must also be abstracted
        // against any refining binder we've already moved into the
        // chain — that's what the inner loop on `j` does for each T_i.
        ExpressionPointer wrappedExpectedType = expectedType;
        for (int i = refiningCount - 1; i >= 0; --i) {
            // abstractOverBoundVariable tracks binder depth itself —
            // we always pass the binder's *outer* BV index (relative
            // to depth = totalBinders), and the function lifts other
            // references for us.
            int outerIdx = refiningBoundVariableIndices[i];
            wrappedExpectedType = abstractOverBoundVariable(
                wrappedExpectedType, outerIdx);
            // T_i is the type of h_i and belongs in the scope at the
            // position where Pi(h_i_new, T_i, ...) is being inserted.
            // The chain places h_1 outermost, h_2 inside it, ..., h_N
            // innermost — so each subsequent outer-abstract (in future
            // iterations) will descend through this Pi's domain at
            // currentDepth=0 and lift its outer BVs by 1, naturally
            // shifting T_i by the number of refining Pis above it.
            // No extra lifting is needed here.
            ExpressionPointer domain = refiningTypesAtOuterDepth[i];
            wrappedExpectedType = makePi(
                cases.refiningNames[i],
                std::move(domain),
                std::move(wrappedExpectedType));
        }

        // (3) Wrap each clause body in `function (h_1) (h_2) … (h_N)
        // => body`. The lambda binders use the same names the user
        // wrote, shadowing the outer same-named binders inside the
        // body. No type annotations on the lambdas — the motive-
        // derived domain tells each lambda what its parameter type is.
        //
        // The shadowing requires the elaborator's opening pass to
        // generate distinct FreeVariable names for the inner lambda
        // binders so unification (e.g., implicit-arg inference inside
        // Equality.symmetry) doesn't confuse them with the outer
        // binders. We rely on openingNameFor's collision-avoidance
        // for that.
        std::vector<SurfaceCasesClause> wrappedClauses;
        for (const auto& clause : cases.clauses) {
            SurfaceExpressionPointer body = clause.body;
            for (int i = refiningCount - 1; i >= 0; --i) {
                SurfaceBinder binder;
                binder.names = {cases.refiningNames[i]};
                binder.type = nullptr;
                binder.isImplicit = false;
                body = makeSurfaceLambda(
                    std::move(binder), body,
                    clause.line, clause.column);
            }
            SurfaceCasesClause wrappedClause;
            wrappedClause.pattern = clause.pattern;
            wrappedClause.body = std::move(body);
            wrappedClause.line = clause.line;
            wrappedClause.column = clause.column;
            wrappedClauses.push_back(std::move(wrappedClause));
        }
        SurfaceExpressionPointer syntheticCases = makeSurfaceCases(
            cases.scrutinee, std::move(wrappedClauses), line, column);

        // (4) Elaborate the synthetic cases against the wrapped Pi
        // chain.
        ExpressionPointer innerCasesKernel = elaborateExpression(
            *syntheticCases, localBinders, wrappedExpectedType);

        // (5) Apply the result to (h_1, h_2, …, h_N), each as a
        // BoundVariable reference into the outer context. The kernel
        // unwinds the Pi chain at the original Goal type.
        for (int i = 0; i < refiningCount; ++i) {
            innerCasesKernel = makeApplication(
                std::move(innerCasesKernel),
                makeBoundVariable(refiningBoundVariableIndices[i]));
        }
        return innerCasesKernel;
    }

    // `note goal : T;` / `note <prop>;` — elaboration-time assertions
    // that don't change the proof state. Both desugar to the rest of
    // the block elaborated at the unchanged expected type, but the
    // elaborator runs a check first:
    //   `note goal : T` — check that the declared T is definitionally
    //     equal to the current expected type. On mismatch, error
    //     pointing at the noted form vs the actual goal.
    //   `note P` — elaborate P as a Proposition and run the
    //     auto-prover on it. If the prover can't close P, error.
    // The returned term is the body's elaboration: nothing about the
    // assertion remains in the produced kernel term.
    ExpressionPointer elaborateNoteExpression(
        const SurfaceNote& note,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "note at line " + std::to_string(line),
            localBinders, expectedType, line, /*column=*/0);
        // `change T;` replaces the goal by `T` for the body (after the
        // defeq check below); `note goal : T;` leaves it unchanged. This
        // holds the replacement goal in the `change` case.
        ExpressionPointer changedGoal;
        if (note.goalType) {
            if (!expectedType) {
                throwElaborate(
                    (note.changesGoal
                         ? "`change T` needs an expected type from "
                           "context (none available at line "
                         : "`note goal : T` needs an expected type from "
                           "context (none available at line ")
                    + std::to_string(line) + ")");
            }
            ExpressionPointer declaredKernel = elaborateExpression(
                *note.goalType, localBinders);
            if (note.changesGoal) changedGoal = declaredKernel;
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            ExpressionPointer declaredOpen = openOverLocalBinders(
                declaredKernel, localBinders, localBinders.size());
            ExpressionPointer expectedOpen = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            if (!isDefinitionallyEqual(
                    environment_, openedContext,
                    declaredOpen, expectedOpen)) {
                throwElaborate(
                    std::string(note.changesGoal
                        ? "`change` mismatch at line "
                        : "`note goal :` mismatch at line ")
                    + std::to_string(line)
                    + " (the given type is not definitionally equal to "
                      "the goal):\n"
                    + (note.changesGoal ? "  change to:     "
                                        : "  noted form:    ")
                    + prettyPrintInLocalScope(declaredKernel, localBinders)
                    + "\n  actual goal:   "
                    + prettyPrintInLocalScope(expectedType, localBinders));
            }
        } else if (note.proposition) {
            ExpressionPointer propKernel = elaborateExpression(
                *note.proposition, localBinders,
                makeSort(makeLevelConst(0)));
            if (note.proof) {
                // `note P by V;` — check the supplied reason V proves P.
                // Like every `note`, it's non-binding (the term is
                // discarded) and never flagged unused/redundant; the `by V`
                // just lets the reason be shown to the reader (and lets the
                // note hold when the auto-prover can't close P on its own).
                ExpressionPointer proofKernel = elaborateExpression(
                    *note.proof, localBinders, propKernel);
                ExpressionPointer proofType = inferTypeInLocalContext(
                    localBinders, proofKernel);
                ExpressionPointer propOpened = openOverLocalBinders(
                    propKernel, localBinders, localBinders.size());
                Context context =
                    buildContextFromLocalBinders(localBinders);
                if (!isDefinitionallyEqual(environment_, context,
                                            proofType, propOpened)) {
                    throwElaborate(
                        std::string("`note P by V` at line ")
                        + std::to_string(line)
                        + ": the proof does not have the noted type `"
                        + prettyPrintInLocalScope(propKernel, localBinders)
                        + "`");
                }
            } else {
                try {
                    (void)autoProveClaim(propKernel, localBinders, line);
                } catch (const ElaborateError&) {
                    throwElaborate(
                        std::string("`note <proposition>` at line ")
                        + std::to_string(line)
                        + ": the auto-prover could not close the noted "
                        "proposition: "
                        + prettyPrintInLocalScope(propKernel, localBinders)
                        + " (supply the reason with `note P by <proof>`)");
                } catch (const TypeError&) {
                    throwElaborate(
                        std::string("`note <proposition>` at line ")
                        + std::to_string(line)
                        + ": the auto-prover raised a type error on the "
                        "noted proposition: "
                        + prettyPrintInLocalScope(propKernel, localBinders));
                }
            }
        } else {
            throwElaborate(
                "internal: SurfaceNote with neither goalType nor "
                "proposition set");
        }
        return elaborateExpression(
            *note.body, localBinders,
            note.changesGoal ? changedGoal : expectedType);
    }

    // `decide P { | yes m => arm_yes | no n => arm_no }` — classical
    // case-split on whether P holds, hiding the auto-transport
    // bookkeeping the user would otherwise write by hand.
    //
    // The expected type Goal must mention `Logic.classical_decidable(P)`
    // structurally (after WHNF + structural deep-β attempts). We
    // abstract that occurrence to form a motive
    //   motive = λ s : Logic.Decidable(P). Goal[s/X]
    // and build the recursor application
    //   Logic.Decidable_recursor.{u}(P, motive, λp. arm_yes, λn. arm_no, X)
    // where `u` is the universe level of Goal (typically 0 since we're
    // proving a Proposition). Each arm body's expected type is
    // motive(yes(p)) / motive(no(n)) — which the kernel β/ι-reduces in
    // surrounding wrappers like `bisectionStepWithDec(…, decision)`,
    // so the user just writes the math witness without any explicit
    // transport.
    ExpressionPointer elaborateDecideExpression(
        const SurfaceDecide& decide,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "decide expression at line " + std::to_string(line));
        TimedScope _scope(*this, "elaborateDecide");
        if (!expectedType) {
            throwElaborate(
                "decide P { … } needs an expected type from context");
        }
        // `decide P { yes m => Y | no n => N }` IS constructor `cases` on
        // `Logic.classical_decidable(P) : Logic.Decidable(P)` — a Type(0)
        // inductive with `yes : P → _` and `no : Not(P) → _`. Desugar to
        // that surface `cases` and reuse the ordinary cases elaboration:
        // the expression-scrutinee path builds the dependent motive (so an
        // arm's expected type ι-reduces with the constructor substituted —
        // e.g. `decide_pick(P, yes(_))` reduces), and each arm body gets the
        // standard coerceToExpectedTypeViaDiff treatment. So a `decide` arm
        // closes exactly what a `cases` arm closes. (This replaced a bespoke
        // ~270-line recursor/motive build that hand-rolled the motive
        // abstraction AND skipped arm coercion — the capability-matrix gap.)
        SurfaceExpressionPointer scrutinee = makeSurfaceApplication(
            makeSurfaceIdentifier("Logic.classical_decidable", {}, line, column),
            std::vector<SurfaceExpressionPointer>{decide.proposition},
            line, column);
        auto armClause = [&](const std::string& constructorName,
                             const std::string& binderName,
                             const SurfaceExpressionPointer& body) {
            std::vector<SurfacePatternPointer> arguments;
            arguments.push_back(makeSurfacePatternBareName(
                binderName.empty() ? std::string("_") : binderName,
                line, column));
            SurfaceCasesClause clause;
            clause.pattern = makeSurfacePatternConstructor(
                constructorName, std::move(arguments), line, column);
            clause.body = body;
            clause.line = line;
            clause.column = column;
            return clause;
        };
        std::vector<SurfaceCasesClause> clauses;
        clauses.push_back(armClause("Logic.Decidable.yes",
            decide.yesBinderName, decide.yesBody));
        clauses.push_back(armClause("Logic.Decidable.no",
            decide.noBinderName, decide.noBody));
        SurfaceExpressionPointer syntheticCases = makeSurfaceCases(
            std::move(scrutinee), std::move(clauses), line, column);
        return elaborateExpression(
            *syntheticCases, localBinders, expectedType);
    }

    // Names of in-scope binders introduced AFTER the `cases`/induction
    // scrutinee whose TYPE depends on it — the hypotheses that an
    // induction must generalize (revert) into the motive, or they keep
    // their stale type referring to the original scrutinee. Returns them
    // in array (outermost-first) order, a valid revert telescope. Empty
    // if the scrutinee isn't a local-binder variable.
    std::vector<std::string> scrutineeDependentBinders(
        const SurfaceExpressionPointer& scrutinee,
        const std::vector<LocalBinder>& localBinders) {
        ExpressionPointer scrutineeKernel;
        try {
            scrutineeKernel =
                elaborateExpression(*scrutinee, localBinders);
        } catch (const ElaborateError&) {
            return {};
        } catch (const TypeError&) {
            return {};
        }
        auto* boundVariable =
            std::get_if<BoundVariable>(&scrutineeKernel->node);
        if (!boundVariable) return {};
        int total = static_cast<int>(localBinders.size());
        int scrutineePosition = total - 1 - boundVariable->deBruijnIndex;
        if (scrutineePosition < 0 || scrutineePosition >= total) return {};
        std::vector<std::string> names;
        for (int i = scrutineePosition + 1; i < total; ++i) {
            // The scrutinee's de Bruijn index within binder i's type
            // scope (binders 0..i-1 are in scope there).
            int scrutineeIndexInTypeScope = (i - 1) - scrutineePosition;
            if (referencesBoundVariable(
                    localBinders[i].type, scrutineeIndexInTypeScope)) {
                names.push_back(localBinders[i].name);
            }
        }
        return names;
    }

    // `cases`/`by_induction` entry. The plain form (no explicit
    // `refining`/`with`) gets an automatic generalize-fallback: if it
    // fails to elaborate AND the scrutinee has in-scope dependent
    // hypotheses, retry reverting them into the motive (via the same
    // `refining` telescope), so an induction over `n` with a hypothesis
    // mentioning `n` no longer needs a hand-written `refining` list.
    // Existing proofs (which elaborate without reverting) take the first
    // path unchanged, so this never regresses them.
    ExpressionPointer elaborateCasesExpression(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        bool plain = cases.refiningNames.empty()
            && cases.equalityHypothesisName.empty();
        if (plain && expectedType) {
            std::vector<std::string> autoRefine =
                scrutineeDependentBinders(cases.scrutinee, localBinders);
            if (!autoRefine.empty()) {
                try {
                    return elaborateCasesExpressionInner(
                        cases, localBinders, expectedType, line, column);
                } catch (const ElaborateError& plainError) {
                    SurfaceCases reverted = cases;
                    reverted.refiningNames = std::move(autoRefine);
                    try {
                        return elaborateCasesExpressionInner(
                            reverted, localBinders, expectedType,
                            line, column);
                    } catch (const ElaborateError&) {
                        // The auto-revert didn't help; surface the
                        // original (more relevant) failure.
                        throw plainError;
                    }
                }
            }
        }
        return elaborateCasesExpressionInner(
            cases, localBinders, expectedType, line, column);
    }

    // `cases scrutinee { | pattern => body | ... }`. Phase 1 covers
    // non-indexed inductives only. Re-uses the existing
    // `buildCaseLambda` helper by synthesizing a minimal pattern-match
    // declaration whose cases mirror the user's clauses.
    ExpressionPointer elaborateCasesExpressionInner(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        // The `cases X refining h1, h2, … { … }` variant lifts the
        // listed binders into the recursor's motive so each arm sees
        // the refined types automatically. Routes through a dedicated
        // desugaring; cannot be combined with `with equalityHypothesisName`
        // (they're orthogonal but no use site has needed both yet).
        if (!cases.refiningNames.empty()) {
            if (!cases.equalityHypothesisName.empty()) {
                throwElaborate(
                    "cases ... with <eq> refining ... is not supported; "
                    "use one or the other");
            }
            return elaborateCasesWithRefining(
                cases, localBinders, expectedType, line, column);
        }
        // The `cases X with equalityHypothesisName { … }` variant
        // routes through a dedicated convoy desugaring; everything
        // below is the plain `cases X { … }` path.
        if (!cases.equalityHypothesisName.empty()) {
            return elaborateCasesWithEqualityHypothesis(
                cases, localBinders, expectedType, line, column);
        }

        Frame frame(*this,
            "cases expression at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "needs an expected type from context — wrap with an "
                "ascription `(cases … : T)` or supply one via context");
        }

        // Elaborate scrutinee + infer + normalise type. The inferred type
        // comes back in "opened" form — local-binder references are
        // Internal-origin FreeVariables. Decompose the opened form to
        // find the inductive head, then close every piece we plan to
        // embed in the motive or pass to buildCaseLambda so they're back
        // in BoundVariable form.
        ExpressionPointer scrutinee =
            elaborateExpression(*cases.scrutinee, localBinders);
        ExpressionPointer scrutineeTypeOpened = weakHeadNormalForm(
            environment_, inferTypeInLocalContext(localBinders, scrutinee));

        std::vector<ExpressionPointer> inductiveArguments;
        ExpressionPointer cursor = scrutineeTypeOpened;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            inductiveArguments.insert(inductiveArguments.begin(),
                                       application->argument);
            cursor = weakHeadNormalForm(environment_, application->function);
        }
        auto* constant = std::get_if<Constant>(&cursor->node);
        if (!constant) {
            throw ElaborateError(
                "cases scrutinee at line " + std::to_string(line)
                + ": type's head is not an inductive constant after "
                "normalisation");
        }
        // Quotient is not an inductive — it's an axiomatic kernel
        // primitive eliminated via `Quotient.induct`. When the scrutinee
        // is a value of `Quotient.{u}(T, R)` and the user supplied a
        // single clause `Quotient.mk(rep) => body`, dispatch to a
        // dedicated handler that builds the induct application directly.
        // This is the "WLOG pick a representative" sugar — the
        // mathematician's natural reading of a quotient elimination.
        if (constant->name == "Quotient") {
            return elaborateQuotientCases(
                cases, scrutinee, scrutineeTypeOpened,
                inductiveArguments, *constant,
                localBinders, expectedType, line, column);
        }
        const Declaration* inductiveDecl =
            environment_.lookup(constant->name);
        auto* inductive = inductiveDecl
            ? std::get_if<Inductive>(inductiveDecl) : nullptr;
        if (!inductive) {
            throw ElaborateError(
                "cases scrutinee at line " + std::to_string(line)
                + ": type '" + constant->name + "' is not an inductive");
        }
        if (static_cast<int>(inductiveArguments.size())
            < inductive->numParameters) {
            throw ElaborateError(
                "cases at line " + std::to_string(line)
                + ": inductive '" + constant->name + "' applied to fewer "
                  "than its parameter count");
        }
        // Close every piece coming out of opened-form inference back to
        // local-binder BoundVariables. The motive and parameterValues
        // passed to buildCaseLambda must live in the same scope as
        // localBinders (BoundVariables, not Internal FreeVariables).
        ExpressionPointer scrutineeType = closeOverLocalBinders(
            scrutineeTypeOpened, localBinders, localBinders.size());
        std::vector<ExpressionPointer> parameterValues;
        for (int p = 0; p < inductive->numParameters; ++p) {
            parameterValues.push_back(closeOverLocalBinders(
                inductiveArguments[p], localBinders,
                localBinders.size()));
        }
        std::vector<ExpressionPointer> indexValues(
            inductiveArguments.begin() + inductive->numParameters,
            inductiveArguments.end());
        // For indexed inductives, each index must be a distinct local
        // variable BoundVariable. The motive will abstract over those
        // variables, and the recursor will take their values back as
        // arguments after the case lambdas.
        std::vector<int> indexLocalIndices;
        for (size_t k = 0; k < indexValues.size(); ++k) {
            // After closeOverLocalBinders the value is in localBinders'
            // BoundVariable form. Look up the index value's variable.
            ExpressionPointer indexClosed = closeOverLocalBinders(
                indexValues[k], localBinders, localBinders.size());
            auto* boundVariable =
                std::get_if<BoundVariable>(&indexClosed->node);
            if (!boundVariable) {
                throw ElaborateError(
                    "cases at line " + std::to_string(line)
                    + ": index " + std::to_string(k)
                    + " of scrutinee type must be a local variable");
            }
            int idx = boundVariable->deBruijnIndex;
            if (idx < 0
                || idx >= static_cast<int>(localBinders.size())) {
                throw ElaborateError(
                    "cases at line " + std::to_string(line)
                    + ": index " + std::to_string(k)
                    + " of scrutinee type references an out-of-scope "
                      "binder");
            }
            for (int seen : indexLocalIndices) {
                if (seen == idx) {
                    throw ElaborateError(
                        "cases at line " + std::to_string(line)
                        + ": the same local variable is used for "
                          "two different scrutinee indices");
                }
            }
            indexLocalIndices.push_back(idx);
            // Replace the opened-form index value with its closed form
            // so downstream code uses local-binder BoundVariables.
            indexValues[k] = indexClosed;
        }
        const std::vector<LevelPointer>& inductiveUniverseArguments =
            constant->universeArguments;

        // Look up the recursor.
        std::string recursorName = constant->name + "_recursor";
        const Declaration* recursorDecl =
            environment_.lookup(recursorName);
        if (!recursorDecl) {
            throw ElaborateError(
                "cases at line " + std::to_string(line)
                + ": no recursor for inductive '" + constant->name + "'");
        }
        auto* recursor = std::get_if<Recursor>(recursorDecl);
        if (!recursor) {
            throw ElaborateError(
                "cases at line " + std::to_string(line)
                + ": '" + recursorName + "' is not a recursor");
        }

        // Build the motive. The structure depends on whether the
        // inductive is indexed and whether the scrutinee is a local
        // variable:
        //
        //   motive = Lambda(idx_0, T_0,
        //              Lambda(idx_1, T_1,
        //                …
        //                Lambda(target, ScrutTypeInMotive,
        //                  expectedType abstracted over [idx_0, …, scrutVar]))).
        //
        // Each index's BoundVariable in expectedType is replaced with
        // the corresponding motive-bound index variable; the
        // scrutinee variable (if local) is replaced with the target
        // binder; other references are shifted up by N+1 (N indices
        // plus 1 target).
        int scrutineeLocalIndex = -1;
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&scrutinee->node)) {
            int index = boundVariable->deBruijnIndex;
            if (index >= 0
                && index < static_cast<int>(localBinders.size())) {
                scrutineeLocalIndex = index;
            }
        }
        // Build the abstraction list: indices first (outermost
        // Lambdas), then the scrutinee variable (innermost / target).
        std::vector<int> abstractionList = indexLocalIndices;
        if (scrutineeLocalIndex >= 0) {
            abstractionList.push_back(scrutineeLocalIndex);
        }
        ExpressionPointer motiveBody;
        if (!abstractionList.empty()) {
            motiveBody =
                abstractOverBoundVariables(expectedType, abstractionList);
        } else if (scrutineeLocalIndex < 0 && indexLocalIndices.empty()) {
            // Expression scrutinee (not a local variable) of a non-indexed
            // inductive: build a DEPENDENT motive by abstracting the
            // scrutinee's structural occurrences in the goal, so each arm's
            // expected type ι-reduces with the constructor substituted for
            // the scrutinee (e.g. `decide` on `Logic.classical_decidable(P)`
            // — the yes arm sees `f(yes(_))` reduced). WHNF-aware so a
            // scrutinee buried behind a δ/ζ-reducible wrapper still matches.
            // When the goal does NOT mention the scrutinee, abstraction
            // finds 0 occurrences and this equals the old constant motive
            // `shift(expectedType, 1)` — so this is purely additive (it only
            // enables the dependent case, which a constant motive rejects).
            ExpressionPointer scrutineeReduced = zetaUnfoldLetBinders(
                scrutinee, localBinders, /*currentDepth=*/0);
            std::string scrutineeHeadName =
                applicationHeadConstantName(scrutineeReduced);
            int occurrences = 0;
            int whnfFuel = 2048;
            motiveWalkerCache_.clear();
            motiveBody = abstractStructuralOccurrenceWithWHNF(
                expectedType, scrutineeReduced, scrutineeHeadName,
                /*currentDepth=*/0, occurrences, whnfFuel);
        } else {
            motiveBody = shift(expectedType, 1);
        }
        // Compute the scrutinee type as it should appear in the
        // motive's target-Lambda position (i.e., after the index
        // Lambdas have been wrapped but before the target Lambda is).
        // The scrutinee type lives in localBinders scope; abstracting
        // it over the indices yields the same value in
        // {localBinders - indices + index_Lambdas} scope.
        ExpressionPointer scrutineeTypeInMotive;
        if (indexLocalIndices.empty()) {
            scrutineeTypeInMotive = scrutineeType;
        } else {
            scrutineeTypeInMotive = abstractOverBoundVariables(
                scrutineeType, indexLocalIndices);
        }
        // Wrap motiveBody with the innermost Lambda (target), using
        // scrutineeTypeInMotive as its domain.
        ExpressionPointer motive = makeLambda(
            "_cases_target", scrutineeTypeInMotive, motiveBody);
        // For each index, wrap with another outer Lambda. We walk in
        // reverse so the OUTERMOST Lambda (indices[0]) ends up last.
        // `indexLocalIndices[k]` is a de Bruijn index; convert to the
        // localBinders array position by inverting against size.
        for (int k = static_cast<int>(indexLocalIndices.size()) - 1;
             k >= 0; --k) {
            int deBruijn = indexLocalIndices[k];
            int arrayPosition = static_cast<int>(localBinders.size())
                - 1 - deBruijn;
            ExpressionPointer indexType =
                localBinders[arrayPosition].type;
            motive = makeLambda(localBinders[arrayPosition].name,
                                 indexType, motive);
        }

        // Infer the motive's universe level by asking the kernel for
        // its type (a Pi ending in a Sort). Local binders' types may
        // reference earlier locals, so open them via openOverLocalBinders.
        LevelPointer motiveLevel;
        {
            Context openedContext = buildContextFromLocalBinders(localBinders);
            ExpressionPointer motiveType =
                inferType(environment_, openedContext,
                           openOverLocalBinders(
                               motive, localBinders,
                               localBinders.size()));
            ExpressionPointer motiveCursor = motiveType;
            while (auto* pi = std::get_if<Pi>(&motiveCursor->node)) {
                motiveCursor = pi->codomain;
            }
            auto* sortNode = std::get_if<Sort>(&motiveCursor->node);
            if (!sortNode) {
                throw ElaborateError(
                    "internal: cases motive type doesn't end in a Sort "
                    "(line " + std::to_string(line) + ")");
            }
            motiveLevel = sortNode->level;
        }

        // Build a synthetic pattern-match declaration so we can reuse
        // buildCaseLambda. Each user clause becomes a SurfacePatternCase
        // with a single pattern. Tuple patterns are first translated to
        // constructor patterns (only meaningful for single-constructor
        // inductives — checked here).
        SurfaceDefinitionDeclaration syntheticDeclaration;
        // The synthetic name is used only by rewriteRecursiveCalls,
        // which looks for calls of this name in the case body. We pick
        // a name no user would write so it can never match.
        syntheticDeclaration.name =
            "_cases_at_line_" + std::to_string(line)
            + "_column_" + std::to_string(column);
        syntheticDeclaration.isTheorem = false;
        for (const auto& clause : cases.clauses) {
            SurfacePatternPointer pattern = clause.pattern;
            SurfaceExpressionPointer body = clause.body;
            if (auto* tupleNode = std::get_if<SurfacePatternTuple>(
                    &pattern->node)) {
                if (inductive->constructorNames.size() != 1) {
                    throw ElaborateError(
                        "cases at line " + std::to_string(clause.line)
                        + ": anonymous tuple pattern '⟨...⟩' only works "
                          "for single-constructor inductives, but '"
                        + constant->name + "' has "
                        + std::to_string(
                            inductive->constructorNames.size())
                        + " constructors");
                }
                const std::string& ctorName =
                    inductive->constructorNames[0];
                const Declaration* ctorDecl =
                    environment_.lookup(ctorName);
                auto* ctorDeclaration = ctorDecl
                    ? std::get_if<Constructor>(ctorDecl) : nullptr;
                if (!ctorDeclaration) {
                    throw ElaborateError(
                        "cases at line " + std::to_string(clause.line)
                        + ": constructor '" + ctorName
                        + "' missing from environment");
                }
                int totalPi = countLeadingPis(ctorDeclaration->type);
                int valueArgCount =
                    totalPi - inductive->numParameters;
                size_t componentCount = tupleNode->components.size();
                if (static_cast<int>(componentCount) == valueArgCount) {
                    pattern = makeSurfacePatternConstructor(
                        ctorName, tupleNode->components,
                        clause.line, clause.column);
                } else if (valueArgCount == 2 && componentCount > 2) {
                    // Right-associate: outer pattern binds first
                    // component directly and a fresh name for the rest;
                    // body is wrapped in an inner cases that
                    // destructures the rest via a tuple pattern with
                    // one fewer component.
                    std::string freshName =
                        "_tupleRest_" + std::to_string(line) + "_"
                        + std::to_string(clause.line) + "_"
                        + std::to_string(clause.column);
                    std::vector<SurfacePatternPointer> outerArgs;
                    outerArgs.push_back(tupleNode->components[0]);
                    outerArgs.push_back(makeSurfacePatternBareName(
                        freshName, clause.line, clause.column));
                    pattern = makeSurfacePatternConstructor(
                        ctorName, std::move(outerArgs),
                        clause.line, clause.column);
                    std::vector<SurfacePatternPointer> restComponents(
                        tupleNode->components.begin() + 1,
                        tupleNode->components.end());
                    SurfacePatternPointer restPattern =
                        makeSurfacePatternTuple(
                            std::move(restComponents),
                            clause.line, clause.column);
                    SurfaceExpressionPointer freshReference =
                        makeSurfaceIdentifier(freshName, {},
                                               clause.line, clause.column);
                    SurfaceCasesClause innerClause;
                    innerClause.pattern = std::move(restPattern);
                    innerClause.body = body;
                    innerClause.line = clause.line;
                    innerClause.column = clause.column;
                    std::vector<SurfaceCasesClause> innerClauses;
                    innerClauses.push_back(std::move(innerClause));
                    body = makeSurfaceCases(
                        std::move(freshReference),
                        std::move(innerClauses),
                        clause.line, clause.column);
                } else {
                    throw ElaborateError(
                        "cases at line " + std::to_string(clause.line)
                        + ": anonymous tuple pattern has "
                        + std::to_string(componentCount)
                        + " component(s) but constructor '" + ctorName
                        + "' takes " + std::to_string(valueArgCount));
                }
            }
            SurfacePatternCase patternCase;
            patternCase.patterns.push_back(std::move(pattern));
            patternCase.body = std::move(body);
            patternCase.line = clause.line;
            patternCase.column = clause.column;
            syntheticDeclaration.cases.push_back(std::move(patternCase));
        }

        // Build a case lambda for each constructor (in declared order).
        std::vector<ExpressionPointer> caseLambdas;
        for (const auto& constructorName : inductive->constructorNames) {
            caseLambdas.push_back(buildCaseLambda(
                syntheticDeclaration, constructorName, constant->name,
                inductiveUniverseArguments, motive, parameterValues,
                localBinders));
        }

        // Assemble the recursor call. For large-eliminating recursors
        // the motive's universe level is an additional universe arg
        // appended after the inductive's own universe args.
        bool recursorHasMotiveLevel =
            recursor->universeParameters.size()
            > inductive->universeParameters.size();
        std::vector<LevelPointer> recursorUniverseArguments =
            inductiveUniverseArguments;
        if (recursorHasMotiveLevel) {
            recursorUniverseArguments.push_back(motiveLevel);
        }
        ExpressionPointer applied =
            makeConstant(recursorName,
                          std::move(recursorUniverseArguments));
        for (const auto& parameterValue : parameterValues) {
            applied = makeApplication(applied, parameterValue);
        }
        applied = makeApplication(applied, motive);
        for (auto& caseLambda : caseLambdas) {
            applied =
                makeApplication(applied, std::move(caseLambda));
        }
        // Apply index values in scrutinee order, then the scrutinee
        // itself. For non-indexed inductives this loop is empty.
        for (const auto& indexValue : indexValues) {
            applied = makeApplication(applied, indexValue);
        }
        applied = makeApplication(applied, scrutinee);
        return applied;
    }

    ExpressionPointer elaborateIdentifier(
        const SurfaceIdentifier& identifier,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {

        for (int i = static_cast<int>(localBinders.size()) - 1; i >= 0; --i) {
            if (localBinders[i].name == identifier.qualifiedName) {
                int deBruijnIndex =
                    static_cast<int>(localBinders.size()) - 1 - i;
                if (!identifier.universeArgs.empty()) {
                    throw ElaborateError(
                        "local variable '" + identifier.qualifiedName
                        + "' cannot take universe arguments (line "
                        + std::to_string(line) + ")");
                }
                return makeBoundVariable(deBruijnIndex);
            }
        }
        bool isCurrentDeclaration =
            !currentDeclarationName_.empty()
            && currentDeclarationName_ == identifier.qualifiedName;
        const Declaration* environmentDeclaration =
            environment_.lookup(identifier.qualifiedName);
        if (!isCurrentDeclaration && !environmentDeclaration) {
            throw ElaborateError(
                "unknown identifier '" + identifier.qualifiedName
                + "' at line " + std::to_string(line)
                + ", column " + std::to_string(column));
        }
        std::vector<LevelPointer> universeArguments;
        if (!identifier.universeArgs.empty()) {
            for (const auto& level : identifier.universeArgs) {
                universeArguments.push_back(elaborateLevel(*level));
            }
        } else if (isCurrentDeclaration
                   && !currentUniverseParametersOrdered_.empty()) {
            // Self-reference auto-fill: when the inductive or theorem
            // currently being declared mentions itself, the universe
            // arguments are exactly its own universe parameters.
            // External references must always be explicit — universe
            // inference is left for a future iteration.
            for (const auto& parameterName :
                 currentUniverseParametersOrdered_) {
                universeArguments.push_back(makeLevelParam(parameterName));
            }
        } else if (environmentDeclaration
                   && universeParameterCount(*environmentDeclaration) > 0) {
            throw ElaborateError(
                "constant '" + identifier.qualifiedName + "' requires "
                + std::to_string(
                      universeParameterCount(*environmentDeclaration))
                + " universe argument(s); supply them explicitly with "
                ".{...} at line " + std::to_string(line));
        }
        return makeConstant(identifier.qualifiedName,
                            std::move(universeArguments));
    }

    // Counts the number of leading Pi binders in a kernel type. Used
    // for under-application detection at constructor call sites.

    // Determines the universe arguments to use when elaborating a
    // constructor call without explicit `.{...}`. Tries, in order:
    //   1. If expectedType reduces to a head Constant for the same
    //      inductive, use its universe arguments.
    //   2. Otherwise, fall back to zeros (suitable for Proposition-
    //      valued inductives; for Type-polymorphic inductives the user
    //      should supply `.{u}` if zeros don't fit).
    std::vector<LevelPointer> universeArgumentsForConstructorCall(
        const Constructor& constructor,
        const Inductive& inductive,
        ExpressionPointer expectedType) {
        const size_t universeParameterCount =
            constructor.universeParameters.size();
        if (universeParameterCount == 0) return {};
        if (expectedType) {
            ExpressionPointer cursor =
                weakHeadNormalForm(environment_, expectedType);
            while (auto* application =
                       std::get_if<Application>(&cursor->node)) {
                cursor = application->function;
            }
            if (auto* constant =
                    std::get_if<Constant>(&cursor->node)) {
                if (constant->name == constructor.inductiveName
                    && constant->universeArguments.size()
                       == universeParameterCount) {
                    return constant->universeArguments;
                }
            }
        }
        (void)inductive;
        std::vector<LevelPointer> zeros;
        for (size_t i = 0; i < universeParameterCount; ++i) {
            zeros.push_back(makeLevelConst(0));
        }
        return zeros;
    }

    // Elaborates a call to a constructor where the user has omitted the
    // inductive's parameter arguments — e.g. `And.introduction(a, b)`
    // instead of `And.introduction(A, B, a, b)`. Infers each parameter
    // by (a) elaborating value args, inferring their types, and
    // unifying against the constructor's value-arg domains, and
    // (b) if any parameters remain unassigned and an expectedType is
    // provided, unifying the constructor's result type against
    // expectedType.
    // Generalised leading-argument inference. Takes a declaration's
    // (universe-substituted) type, the count of leading Pis to treat as
    // inferable metavariables, and the user-supplied trailing arguments.
    // Returns a vector of inferred kernel terms for the leading positions
    // (in declaration order) plus a vector of elaborated trailing args.
    //
    // The unification machinery is shared with constructor parameter
    // inference: open the leading Pis as Internal-origin FreeVariables,
    // backward-unify the result type against `expectedType` if available,
    // then elaborate each trailing arg in order and unify its inferred
    // type against the Pi domain (with previously-resolved metavariables
    // substituted).
    struct CallInferenceResult {
        std::vector<ExpressionPointer> leadingValues;     // inferred
        std::vector<ExpressionPointer> trailingValues;    // user args
    };
    CallInferenceResult inferLeadingArguments(
        const std::string& diagnosticName,
        ExpressionPointer instantiatedDeclarationType,
        int numLeadingToInfer,
        const std::vector<SurfaceExpressionPointer>& trailingArgumentsSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        const std::string& metavariablePrefix,
        int line) {

        // Open each leading Pi with an Internal-origin FreeVariable
        // serving as a metavariable.
        std::vector<std::string> leadingFreshNames;
        std::set<std::string> metavariableNames;
        // The i-th leading binder's domain, expressed with the earlier
        // leading metavariables (fresh FreeVariables) substituted in.
        // Used by the canonical-instance resolution pass below.
        std::vector<ExpressionPointer> leadingDomains;
        ExpressionPointer cursor = instantiatedDeclarationType;
        for (int i = 0; i < numLeadingToInfer; ++i) {
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) {
                throw ElaborateError(
                    "internal: declaration '" + diagnosticName
                    + "' has fewer leading Pis than expected (line "
                    + std::to_string(line) + ")");
            }
            std::string fresh =
                metavariablePrefix + std::to_string(i) + "_"
                + diagnosticName;
            leadingFreshNames.push_back(fresh);
            metavariableNames.insert(fresh);
            leadingDomains.push_back(pi->domain);
            cursor = openBinder(pi->codomain, fresh,
                                 FreeVariableOrigin::Internal);
        }

        // Backward inference FIRST, before elaborating trailing args.
        // Open every trailing-arg Pi as well (with Internal FreeVars
        // distinct from the leading metavariables), then unify the
        // result against `expectedType` if it was supplied. This lets
        // the trailing-arg elaborations below see fully-resolved
        // expected domain types, which is essential for nested
        // under-applied calls.
        std::map<std::string, ExpressionPointer> assignment;
        if (expectedType) {
            ExpressionPointer resultProbe = cursor;
            for (size_t j = 0;
                 j < trailingArgumentsSurface.size(); ++j) {
                auto* pi = std::get_if<Pi>(&resultProbe->node);
                if (!pi) break;
                std::string trailingArgumentFresh =
                    "_callTrailingArgument_" + std::to_string(j);
                resultProbe = openBinder(pi->codomain,
                                          trailingArgumentFresh,
                                          FreeVariableOrigin::Internal);
            }
            // Structural match first, without unfolding. Works when
            // both sides share the same head.
            unifyConstructorParameters(resultProbe, expectedType,
                                          metavariableNames, assignment);
            // If anything's still unassigned, WHNF both sides and try
            // again. This handles Definition-headed types (e.g.
            // `Natural.divides(_, _)`) by unfolding them to their
            // underlying structure (`Exists(...)`) — metavariables
            // pushed under Lambda binders are now safe to assign,
            // because the unifier shifts them back to the outer scope.
            bool anyLeftUnassigned = false;
            for (const auto& name : leadingFreshNames) {
                if (!assignment.count(name)) {
                    anyLeftUnassigned = true; break;
                }
            }
            if (anyLeftUnassigned) {
                ExpressionPointer expectedTypeNormalised =
                    weakHeadNormalForm(environment_, expectedType);
                ExpressionPointer resultProbeNormalised =
                    weakHeadNormalForm(environment_, resultProbe);
                unifyConstructorParameters(resultProbeNormalised,
                                              expectedTypeNormalised,
                                              metavariableNames, assignment);
            }
        }

        // Walk trailing-arg Pis. For each, elaborate the corresponding
        // surface argument, infer its kernel type, and unify the
        // (metavariable-substituted) Pi domain against the inferred
        // type to fill in any leading values that backward inference
        // didn't resolve. Then descend through the Pi.
        std::vector<ExpressionPointer> elaboratedTrailingArguments;
        for (size_t j = 0; j < trailingArgumentsSurface.size(); ++j) {
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) {
                throw ElaborateError(
                    "call to '" + diagnosticName
                    + "': too many arguments at line "
                    + std::to_string(line));
            }
            ExpressionPointer expectedDomain =
                substituteFreeVariables(pi->domain, assignment);
            // If the expected domain still mentions an unresolved leading
            // metavariable, do NOT hand it to the trailing-arg
            // elaboration: a nested call to the same (or a related)
            // implicit-leading function would backward-bind its own
            // implicits to OUR metavariables, leaving them unresolved —
            // they then leak into the emitted term as unbound
            // FreeVariables (e.g. `PAdic.add(PAdic.add(x, y), z)`).
            // Elaborate the argument bottom-up to a concrete type instead;
            // the unification below still uses `expectedDomain` to solve
            // the metavariables from that concrete type.
            ExpressionPointer expectedForArgument =
                containsNamedFreeVariable(expectedDomain, metavariableNames)
                    ? nullptr
                    : expectedDomain;
            ExpressionPointer kernelTrailingArgument = elaborateExpression(
                *trailingArgumentsSurface[j], localBinders,
                expectedForArgument);
            // Infer the trailing arg's type WITHOUT normalising first, so a
            // Definition head (e.g. `Rational.LessOrEqual` for an `a ≤ b`
            // domain) is preserved and matches the Pi domain's head
            // structurally. WHNF only as a fallback below — this mirrors
            // the backward path above. WHNF-ing up front unfolds `a ≤ b`
            // to its `IsNonneg(…)`/`Exists(…)` body, whose head no longer
            // matches the `≤`-shaped domain, leaving the leading
            // metavariables for `a`/`b` unassigned and the whole inference
            // failing for nested calls with no propagated expected type
            // (e.g. `Rational.LessOrEqual.sum(p1, p2)` as a `rewrite` term).
            ExpressionPointer inferredArgumentType =
                closeOverLocalBinders(
                    inferTypeInLocalContext(
                        localBinders, kernelTrailingArgument),
                    localBinders, localBinders.size());
            // Structural attempt first; WHNF both sides as fallback
            // for Definition-headed mismatches. We pass a binder-type
            // stack so the unifier can apply Miller-pattern HO
            // unification when it descends into Pi/Lambda binders and
            // a metavariable head is applied to a local-binder
            // BoundVariable.
            std::vector<ExpressionPointer> binderStack;
            unifyConstructorParameters(expectedDomain,
                                          inferredArgumentType,
                                          metavariableNames, assignment,
                                          0, &binderStack);
            bool anyLeftUnassigned = false;
            for (const auto& name : leadingFreshNames) {
                if (!assignment.count(name)) {
                    anyLeftUnassigned = true; break;
                }
            }
            if (anyLeftUnassigned) {
                ExpressionPointer expectedDomainNormalised =
                    weakHeadNormalForm(environment_, expectedDomain);
                ExpressionPointer inferredArgumentTypeRenormalised =
                    weakHeadNormalForm(environment_,
                                        inferredArgumentType);
                binderStack.clear();
                unifyConstructorParameters(expectedDomainNormalised,
                                              inferredArgumentTypeRenormalised,
                                              metavariableNames, assignment,
                                              0, &binderStack);
            }
            elaboratedTrailingArguments.push_back(kernelTrailingArgument);
            std::string trailingArgumentFresh =
                "_callTrailingArgument_" + std::to_string(j);
            // Bind the trailing-arg placeholder to its elaborated
            // value so that subsequent expectedDomain substitutions for
            // later trailing args (and the final result-pattern
            // unification) don't leak `_callTrailingArgument_N`
            // placeholders into nested constructor inferences — those
            // placeholders would otherwise block assignments via the
            // `containsValueArgumentFreeVar` guard in
            // unifyConstructorParameters.
            assignment[trailingArgumentFresh] = kernelTrailingArgument;
            cursor = openBinder(pi->codomain, trailingArgumentFresh,
                                 FreeVariableOrigin::Internal);
        }

        // Instance resolution (Stage 3 + local-instance follow-on). For
        // any still-unassigned leading implicit whose domain is a
        // PREDICATE application (a structure class like IsGroup/IsRing —
        // head Definition returning Proposition), resolve it either from
        // the canonical-instance registry (concrete or parameterized
        // carrier) OR from a UNIQUE in-scope hypothesis (abstract carrier);
        // either way the sibling operation/identity/… implicits are filled
        // by unifying the chosen instance's type against the domain. The
        // predicate gate keeps ordinary implicits (`{T : Type(0)}`,
        // `{x : Tagged(m)}`) untouched.
        {
            bool madeProgress = true;
            while (madeProgress) {
                madeProgress = false;
                for (int i = 0; i < numLeadingToInfer; ++i) {
                    const std::string& metaName = leadingFreshNames[i];
                    if (assignment.count(metaName)) continue;
                    ExpressionPointer domain = substituteFreeVariables(
                        leadingDomains[i], assignment);
                    std::string structureName = headConstantName(domain);
                    if (structureName == "<unknown>") continue;
                    if (!structureHeadIsClass(structureName)) continue;
                    // First argument of the structure application is the
                    // carrier; collect the spine and read it off.
                    ExpressionPointer spine = domain;
                    ExpressionPointer carrierArgument;
                    while (auto* application =
                               std::get_if<Application>(&spine->node)) {
                        carrierArgument = application->argument;
                        spine = application->function;
                    }
                    if (!carrierArgument) continue;
                    std::string carrierName =
                        headConstantName(carrierArgument);

                    // --- Registry path. Open the instance's leading
                    // parameter Pis as fresh metavariables and unify the
                    // resulting structure application against the domain.
                    // This solves the parameters from WHEREVER they appear
                    // — in the carrier (`IsGroup(IntegerMod(m), …)`) or in
                    // the relation (`IsEquivalenceRelation(Integer,
                    // CongruentModulo(m))`) — and fills the domain's own
                    // sibling metavariables. The instance is then emitted
                    // applied to the solved parameters.
                    auto entry = (carrierName == "<unknown>")
                        ? environment_.canonicalInstanceRegistry.end()
                        : environment_.canonicalInstanceRegistry.find(
                              std::make_tuple(structureName, carrierName));
                    if (entry != environment_.canonicalInstanceRegistry.end()
                        && entry->second.universeParameters.empty()) {
                        std::set<std::string> parameterMetavariables =
                            metavariableNames;
                        std::vector<std::string> parameterMetaNames;
                        ExpressionPointer openedInstanceType =
                            entry->second.type;
                        bool opened = true;
                        for (int k = 0; k < entry->second.parameterCount;
                             ++k) {
                            auto* pi = std::get_if<Pi>(
                                &openedInstanceType->node);
                            if (!pi) { opened = false; break; }
                            std::string fresh = "_instanceParameter_"
                                + std::to_string(k) + "_"
                                + entry->second.termName;
                            parameterMetavariables.insert(fresh);
                            parameterMetaNames.push_back(fresh);
                            openedInstanceType = openBinder(
                                pi->codomain, fresh,
                                FreeVariableOrigin::Internal);
                        }
                        if (opened) {
                            std::map<std::string, ExpressionPointer>
                                instanceAssignment = assignment;
                            // unifyConstructorParameters solves the
                            // metavariables in its FIRST argument. Run both
                            // directions: domain-first solves the domain's
                            // sibling metavariables (operation/identity/…)
                            // from the instance; instance-first solves the
                            // instance's parameters from the domain.
                            unifyConstructorParameters(
                                domain, openedInstanceType,
                                parameterMetavariables, instanceAssignment);
                            unifyConstructorParameters(
                                openedInstanceType, domain,
                                parameterMetavariables, instanceAssignment);
                            bool allSolved = true;
                            for (const auto& p : parameterMetaNames) {
                                if (!instanceAssignment.count(p)) {
                                    allSolved = false; break;
                                }
                            }
                            if (allSolved) {
                                // Merge the sibling domain-metavariable
                                // solutions (substituting the parameters)
                                // into the real assignment.
                                for (const auto& nm : leadingFreshNames) {
                                    if (assignment.count(nm)) continue;
                                    auto it = instanceAssignment.find(nm);
                                    if (it != instanceAssignment.end()) {
                                        assignment[nm] =
                                            substituteFreeVariables(
                                                it->second,
                                                instanceAssignment);
                                    }
                                }
                                ExpressionPointer instanceTerm =
                                    makeConstant(entry->second.termName);
                                for (const auto& p : parameterMetaNames) {
                                    instanceTerm = makeApplication(
                                        std::move(instanceTerm),
                                        instanceAssignment[p]);
                                }
                                assignment[metaName] =
                                    std::move(instanceTerm);
                                madeProgress = true;
                                continue;
                            }
                        }
                    }

                    // --- Local-hypothesis path: abstract carrier. Find a
                    // UNIQUE in-scope binder whose type is the same
                    // structure on a matching carrier; use it as the
                    // instance and read its operations off to fill the
                    // sibling implicits. Work in opened form (FreeVariables
                    // for the local binders), then close the solved values
                    // back; reject on a non-unique match.
                    ExpressionPointer domainOpened = openOverLocalBinders(
                        domain, localBinders, localBinders.size());
                    Context hypothesisContext =
                        buildContextFromLocalBinders(localBinders);
                    int matchCount = 0;
                    int matchBinder = -1;
                    std::map<std::string, ExpressionPointer> matchTrial;
                    for (int j =
                             static_cast<int>(localBinders.size()) - 1;
                         j >= 0; --j) {
                        ExpressionPointer candidateType =
                            openOverLocalBinders(
                                localBinders[j].type, localBinders,
                                static_cast<size_t>(j));
                        if (headConstantName(candidateType)
                            != structureName) {
                            continue;
                        }
                        std::map<std::string, ExpressionPointer> trial;
                        std::vector<ExpressionPointer> binderStack;
                        unifyConstructorParameters(
                            domainOpened, candidateType, metavariableNames,
                            trial, 0, &binderStack);
                        ExpressionPointer resolved =
                            substituteFreeVariables(domainOpened, trial);
                        if (!isDefinitionallyEqual(
                                environment_, hypothesisContext,
                                resolved, candidateType)) {
                            continue;
                        }
                        ++matchCount;
                        matchBinder = j;
                        matchTrial = trial;
                        if (matchCount > 1) break;
                    }
                    if (matchCount == 1) {
                        for (const auto& solvedValue : matchTrial) {
                            if (!assignment.count(solvedValue.first)) {
                                assignment[solvedValue.first] =
                                    closeOverLocalBinders(
                                        solvedValue.second, localBinders,
                                        localBinders.size());
                            }
                        }
                        assignment[metaName] = makeBoundVariable(
                            static_cast<int>(localBinders.size()) - 1
                            - matchBinder);
                        madeProgress = true;
                    }
                }
            }
        }

        // If any leading value still remains unassigned after forward
        // inference, retry the backward unification (now potentially
        // using newly-derived information).
        bool anyUnassigned = false;
        for (const auto& name : leadingFreshNames) {
            if (!assignment.count(name)) { anyUnassigned = true; break; }
        }
        if (anyUnassigned && expectedType) {
            ExpressionPointer resultPattern =
                substituteFreeVariables(cursor, assignment);
            ExpressionPointer expectedTypeNormalised =
                weakHeadNormalForm(environment_, expectedType);
            unifyConstructorParameters(resultPattern,
                                          expectedTypeNormalised,
                                          metavariableNames, assignment);
        }

        // A leading value derived by backward unification against an
        // expectedType that was OPENED over the local binders (e.g. the
        // generic-application path passes `pi->domain` from
        // inferTypeInLocalContext, which is opened) is a pure local-binder
        // FreeVariable term — it must be CLOSED back to BoundVariable form
        // before it is emitted, or the kernel sees an unbound internal
        // variable (`weak(Rational.LessThan.weaken(h))`). Forward-derived
        // values are already closed and contain no such FreeVariable, so
        // they are left untouched (closing them would over-shift their
        // BoundVariables). The two never mix in one value.
        std::set<std::string> localBinderOpeningNames;
        for (size_t b = 0; b < localBinders.size(); ++b) {
            localBinderOpeningNames.insert(openingNameFor(localBinders, b));
        }
        CallInferenceResult result;
        std::vector<std::string> unassigned;
        std::vector<std::pair<std::string, ExpressionPointer>> assigned;
        for (const auto& name : leadingFreshNames) {
            auto iterator = assignment.find(name);
            if (iterator == assignment.end()) {
                unassigned.push_back(name);
            } else {
                ExpressionPointer value = iterator->second;
                if (containsNamedFreeVariable(value,
                                              localBinderOpeningNames)) {
                    value = closeOverLocalBinders(
                        value, localBinders, localBinders.size());
                }
                assigned.push_back({name, value});
                result.leadingValues.push_back(value);
            }
        }
        if (!unassigned.empty()) {
            std::string message =
                "could not infer all leading arguments of '"
                + diagnosticName + "':";
            for (const auto& name : unassigned) {
                // Names are like `_callLeadingArgument_2_Foo`; the
                // index after the prefix tells the user which
                // declaration parameter the elaborator gave up on.
                message += "\n    position ";
                size_t firstUnderscore = name.find('_', 1);
                size_t secondUnderscore = name.find(
                    '_', firstUnderscore + 1);
                if (firstUnderscore != std::string::npos
                    && secondUnderscore != std::string::npos) {
                    message += name.substr(
                        firstUnderscore + 1,
                        secondUnderscore - firstUnderscore - 1);
                } else {
                    message += "(?)";
                }
                message += " is unassigned";
            }
            if (!assigned.empty()) {
                message += "\n  inferred so far:";
                for (const auto& pair : assigned) {
                    message += "\n    ";
                    size_t firstUnderscore = pair.first.find('_', 1);
                    size_t secondUnderscore = pair.first.find(
                        '_', firstUnderscore + 1);
                    if (firstUnderscore != std::string::npos
                        && secondUnderscore != std::string::npos) {
                        message += "position ";
                        message += pair.first.substr(
                            firstUnderscore + 1,
                            secondUnderscore - firstUnderscore - 1);
                    } else {
                        message += pair.first;
                    }
                    message += " = ";
                    message += prettyPrintInLocalScope(
                        pair.second, localBinders);
                }
            }
            if (expectedType) {
                message += "\n  expected return type: ";
                message += prettyPrintInLocalScope(
                    expectedType, localBinders);
            }
            message += "\n  Provide the missing argument(s) explicitly "
                       "to disambiguate.";
            throwElaborate(message);
        }
        result.trailingValues = std::move(elaboratedTrailingArguments);
        return result;
    }

    // True when `openedType` (already opened over `localBinders`) is a
    // Proposition — i.e. its own type weak-head-reduces to `Sort 0`. Used
    // to restrict context-discharge to proof obligations, never values.
    bool typeIsProposition(const Context& context,
                            const ExpressionPointer& openedType) {
        try {
            ExpressionPointer typeOfType =
                inferType(environment_, context, openedType);
            ExpressionPointer reduced =
                weakHeadNormalForm(environment_, typeOfType);
            auto* sortNode = std::get_if<Sort>(&reduced->node);
            if (!sortNode) return false;
            auto* constant =
                std::get_if<LevelConst>(&sortNode->level->node);
            return constant && constant->value == 0;
        } catch (...) {
            return false;
        }
    }

    // ---- `by (<fact>)`: cite a proposition where a proof is expected ----
    //
    // The user writes `by (P)` with `P` a proposition (a fact) rather than a
    // proof. We auto-prove `P` and hand the synthesized proof to the very
    // same machinery that handles `by <proof-of-P>`, so a cited fact bridges
    // to the goal through identical unify / ring / rewrite paths. A proof
    // term has a proposition as its type, whereas a proposition's own type is
    // the `Proposition` sort — that gap is the dispatch.

    // True iff `term` (in the `localBinders` scope) is itself a proposition —
    // i.e. its type is the `Proposition` sort (`Sort 0`). A proof term fails
    // this (its type is a proposition, not the sort), which is exactly the
    // dispatch between "fact cited" and "proof supplied". Uses
    // `inferTypeInLocalContext` so it matches the opened representation the
    // surrounding calc/claim code uses (a raw `inferType` over a freshly built
    // context mishandles the opened form).
    bool termIsProposition(
        const std::vector<LocalBinder>& localBinders,
        const ExpressionPointer& term) {
        ExpressionPointer termType;
        try {
            termType = inferTypeInLocalContext(localBinders, term);
        } catch (...) {
            return false;
        }
        ExpressionPointer reduced =
            weakHeadNormalForm(environment_, termType);
        auto* sortNode = std::get_if<Sort>(&reduced->node);
        if (!sortNode) return false;
        auto* constant =
            std::get_if<LevelConst>(&sortNode->level->node);
        return constant && constant->value == 0;
    }

    // Auto-prove a cited proposition; clear error if the prover can't reach it.
    ExpressionPointer proveCitedFact(
        const ExpressionPointer& factProposition,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        try {
            return autoProveClaim(factProposition, localBinders, line);
        } catch (const ElaborateError&) {
        } catch (const TypeError&) {
        }
        throwElaborate(
            "`by (<fact>)`: couldn't prove the cited fact `"
            + prettyPrintInLocalScope(factProposition, localBinders)
            + "` — the auto-prover can't reach it on its own. Establish it "
            "with its own `claim …;` (or give `by <proof>`) instead.");
    }

    // True iff `result` actually has type `goalClosed` in the local scope.
    // Guarded: a malformed bridge result (or any inference failure) reads as
    // "doesn't prove the goal" rather than crashing.
    bool bridgedResultProvesGoal(
        const ExpressionPointer& result,
        const ExpressionPointer& goalClosed,
        const std::vector<LocalBinder>& localBinders) {
        try {
            ExpressionPointer resultType =
                inferTypeInLocalContext(localBinders, result);
            ExpressionPointer goalOpened = openOverLocalBinders(
                goalClosed, localBinders, localBinders.size());
            Context context = buildContextFromLocalBinders(localBinders);
            return isDefinitionallyEqual(
                environment_, context, resultType, goalOpened);
        } catch (...) {
            return false;
        }
    }

    // Given a cited proposition `factProposition` and a `goalClosed`, prove
    // the fact and bridge its proof to the goal exactly like `by <proof-of-
    // fact>`: first the goal-driven hint pipeline (unify conclusion / fill
    // args), then the diff-congruence path (`f(a) = f(b)` from `a = b`).
    ExpressionPointer bridgeCitedFact(
        const ExpressionPointer& factProposition,
        const ExpressionPointer& goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer proof =
            proveCitedFact(factProposition, localBinders, line);
        // `proof : factProposition` by construction, so use the cited
        // proposition as its (closed) type directly — re-inferring is both
        // unnecessary and unsafe (the auto-prover's result form differs from
        // an elaborated term and can confuse `inferTypeInLocalContext`).
        // Each bridge candidate is *validated* against the goal: a diff that
        // the bridge cannot handle (e.g. a symmetry flip) can return a
        // malformed term rather than throwing, which would crash downstream.
        ExpressionPointer candidate;
        try {
            candidate = autoFillHintForClaim(
                proof, factProposition, goalClosed, localBinders, line);
        } catch (...) { candidate = nullptr; }
        if (candidate && bridgedResultProvesGoal(
                candidate, goalClosed, localBinders)) {
            return candidate;
        }
        try {
            candidate = coerceToExpectedTypeViaDiff(
                localBinders, proof, goalClosed);
        } catch (...) { candidate = nullptr; }
        if (candidate && bridgedResultProvesGoal(
                candidate, goalClosed, localBinders)) {
            return candidate;
        }
        throwElaborate(
            "`by (<fact>)`: proved `"
            + prettyPrintInLocalScope(factProposition, localBinders)
            + "` but it does not establish the goal — the cited fact must be "
            "(or bridge by ring / rewrite / congruence to) the goal.");
    }

    // Claim-path recovery when the direct hint pipeline didn't close the
    // goal. If the hint was a cited fact (a Proposition), prove it and bridge
    // its proof to the goal; otherwise fall back to the diff-congruence path
    // on the hint re-elaborated at the goal type — the behaviour the named-
    // claim path always had.
    ExpressionPointer recoverClaimHint(
        const ExpressionPointer& hintTerm,
        const SurfaceExpression& byHint,
        const ExpressionPointer& goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        if (hintTerm && termIsProposition(localBinders, hintTerm)) {
            return bridgeCitedFact(
                hintTerm, goalClosed, localBinders, line);
        }
        return coerceToExpectedTypeViaDiff(
            localBinders,
            elaborateExpression(byHint, localBinders, goalClosed),
            goalClosed);
    }

    // Like `inferLeadingArguments` but the holes can be at ANY position,
    // marked by `?` in the user's argument list. For each position:
    //   - If it's `?` (SurfaceHole): open a metavariable; resolve it
    //     later via backward inference (unify result type against goal)
    //     plus forward inference (unify other args' inferred types
    //     against their domains).
    //   - If it's a real surface expression: elaborate it against the
    //     Pi domain (with prior metas substituted), unify the inferred
    //     type against the domain.
    // After all args processed, do a final backward unification to fill
    // any holes not yet resolved by the per-arg forward pass.
    //
    // Returns the resolved arg values by position. Errors if any hole
    // remains unassigned (with a diagnostic message naming the position).
    std::vector<ExpressionPointer> inferCallWithHoles(
        const std::string& diagnosticName,
        ExpressionPointer instantiatedFunctionType,
        const std::vector<SurfaceExpressionPointer>& surfaceArgs,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {

        lastDischarges_.clear();
        // Step 1: walk the function's Pi chain. At each position, allocate
        // a fresh Internal FreeVariable. Hole positions add their name to
        // `metavariableNames` (to be resolved by unification); non-hole
        // positions get a name that's later bound to the elaborated value.
        std::vector<std::string> argFreshNames;
        std::vector<bool> isHole;
        std::set<std::string> metavariableNames;
        std::vector<ExpressionPointer> piDomains;
        std::vector<ExpressionPointer> piCodomainsBeforeOpen;
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, instantiatedFunctionType);
        for (size_t i = 0; i < surfaceArgs.size(); ++i) {
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) {
                throw ElaborateError(
                    "call to '" + diagnosticName
                    + "': too many arguments at line "
                    + std::to_string(line));
            }
            bool argIsHole = std::holds_alternative<SurfaceHole>(
                surfaceArgs[i]->node);
            std::string fresh = (argIsHole ? "_hole_" : "_arg_")
                                + std::to_string(i) + "_" + diagnosticName;
            argFreshNames.push_back(fresh);
            isHole.push_back(argIsHole);
            piDomains.push_back(pi->domain);
            piCodomainsBeforeOpen.push_back(pi->codomain);
            if (argIsHole) metavariableNames.insert(fresh);
            cursor = weakHeadNormalForm(environment_,
                openBinder(pi->codomain, fresh,
                            FreeVariableOrigin::Internal));
        }
        // cursor is the result type with all positions opened as FVs.
        ExpressionPointer resultTypePattern = cursor;

        // Step 2: backward inference. Unify the result type pattern
        // against the expected type to fix as many hole metavariables
        // as possible up front.
        std::map<std::string, ExpressionPointer> assignment;
        if (expectedType) {
            unifyConstructorParameters(resultTypePattern, expectedType,
                                          metavariableNames, assignment);
            // If anything's still unassigned, try with both sides WHNF'd.
            bool anyUnassigned = false;
            for (const auto& name : metavariableNames) {
                if (!assignment.count(name)) {
                    anyUnassigned = true; break;
                }
            }
            if (anyUnassigned) {
                ExpressionPointer resultPatternNormalised =
                    weakHeadNormalForm(environment_, resultTypePattern);
                ExpressionPointer expectedTypeNormalised =
                    weakHeadNormalForm(environment_, expectedType);
                unifyConstructorParameters(resultPatternNormalised,
                                              expectedTypeNormalised,
                                              metavariableNames, assignment);
            }
            // Class-equality relaxation (WS3): when the goal is
            // `mk(x) = mk(y)` but this function concludes in the underlying
            // relation `R`, unify the result pattern against `R(x, y)` so
            // the holes fill. The result then has type `R(x, y)`, and the
            // equality-of-classes coercion wraps it in Quotient.sound.
            anyUnassigned = false;
            for (const auto& name : metavariableNames) {
                if (!assignment.count(name)) { anyUnassigned = true; break; }
            }
            if (anyUnassigned) {
                if (ExpressionPointer relaxed =
                        relaxClassEqualityToEquivalence(expectedType)) {
                    unifyConstructorParameters(
                        weakHeadNormalForm(environment_, resultTypePattern),
                        weakHeadNormalForm(environment_, relaxed),
                        metavariableNames, assignment);
                }
            }
        }

        // Step 3: forward inference. For each non-hole arg, elaborate it
        // against the Pi domain (with prior metas substituted), unify the
        // inferred type against the domain to fix more hole metas. Bind
        // each non-hole arg's placeholder to its elaborated value so
        // subsequent domains substitute correctly.
        std::vector<ExpressionPointer> elaboratedArgs(surfaceArgs.size(),
                                                       nullptr);
        for (size_t i = 0; i < surfaceArgs.size(); ++i) {
            ExpressionPointer expectedDomain =
                substituteFreeVariables(piDomains[i], assignment);
            if (isHole[i]) continue;
            ExpressionPointer kernelArg = elaborateExpression(
                *surfaceArgs[i], localBinders, expectedDomain);
            ExpressionPointer inferredType =
                weakHeadNormalForm(environment_,
                    inferTypeInLocalContext(
                        localBinders, kernelArg));
            inferredType = closeOverLocalBinders(
                inferredType, localBinders, localBinders.size());
            std::vector<ExpressionPointer> binderStack;
            unifyConstructorParameters(expectedDomain, inferredType,
                                          metavariableNames, assignment,
                                          0, &binderStack);
            bool anyUnassigned = false;
            for (const auto& name : metavariableNames) {
                if (!assignment.count(name)) {
                    anyUnassigned = true; break;
                }
            }
            if (anyUnassigned) {
                ExpressionPointer expectedDomainNormalised =
                    weakHeadNormalForm(environment_, expectedDomain);
                ExpressionPointer inferredRenormalised =
                    weakHeadNormalForm(environment_, inferredType);
                binderStack.clear();
                unifyConstructorParameters(expectedDomainNormalised,
                                              inferredRenormalised,
                                              metavariableNames, assignment,
                                              0, &binderStack);
            }
            elaboratedArgs[i] = kernelArg;
            // Bind this arg's placeholder so later domain substitutions
            // (and the final result pattern unification) see the actual
            // value rather than the FV placeholder.
            assignment[argFreshNames[i]] = kernelArg;
        }

        // Step 4: final backward unification — any holes still
        // unassigned now potentially have more constraints to work with.
        bool anyUnassigned = false;
        for (const auto& name : metavariableNames) {
            if (!assignment.count(name)) { anyUnassigned = true; break; }
        }
        if (anyUnassigned && expectedType) {
            ExpressionPointer resultPatternResolved =
                substituteFreeVariables(resultTypePattern, assignment);
            ExpressionPointer expectedNormalised =
                weakHeadNormalForm(environment_, expectedType);
            unifyConstructorParameters(resultPatternResolved,
                                          expectedNormalised,
                                          metavariableNames, assignment);
        }

        // Step 5: resolve holes from the assignment. Build the final
        // arg list by substituting metavariables.
        std::vector<size_t> unresolved;
        for (size_t i = 0; i < surfaceArgs.size(); ++i) {
            if (isHole[i]) {
                auto iterator = assignment.find(argFreshNames[i]);
                if (iterator == assignment.end()) {
                    unresolved.push_back(i);
                } else {
                    elaboratedArgs[i] = iterator->second;
                }
            }
        }
        // Step 5b: discharge leftover PROOF holes from in-scope hypotheses.
        // A hole the goal didn't pin is typically a side-condition proof
        // argument of a named lemma cited as `by L` (desugared to
        // `L(?, …, ?)`): the conclusion fixes the value holes, leaving a
        // propositional precondition the goal never mentions. If a proof of
        // that exact proposition is already available in the local context,
        // use it — the same precondition discharge the rewrite-lemma index
        // performs (`tryLemmaIndexLookup`). Gated to Prop-typed slots whose
        // type is fully determined (no remaining unresolved hole), so an
        // open VALUE hole — which must come from the goal — is never
        // guessed from context.
        if (!unresolved.empty()) {
            std::set<std::string> stillUnresolvedNames;
            for (size_t idx : unresolved) {
                stillUnresolvedNames.insert(argFreshNames[idx]);
            }
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            std::vector<size_t> remaining;
            for (size_t i : unresolved) {
                ExpressionPointer slotType =
                    substituteFreeVariables(piDomains[i], assignment);
                if (containsNamedFreeVariable(slotType,
                                              stillUnresolvedNames)) {
                    remaining.push_back(i);
                    continue;
                }
                ExpressionPointer slotOpened;
                ExpressionPointer slotNormalised;
                try {
                    slotOpened = openOverLocalBinders(
                        slotType, localBinders, localBinders.size());
                    slotNormalised = weakHeadNormalForm(
                        environment_, slotOpened);
                } catch (const TypeError&) {
                    remaining.push_back(i);
                    continue;
                }
                if (!typeIsProposition(openedContext, slotNormalised)) {
                    remaining.push_back(i);
                    continue;
                }
                bool found = false;
                for (int j = static_cast<int>(localBinders.size()) - 1;
                     j >= 0; --j) {
                    ExpressionPointer candidateType =
                        openOverLocalBinders(
                            localBinders[j].type, localBinders, j);
                    bool eq;
                    try {
                        eq = isDefinitionallyEqual(
                            environment_, openedContext,
                            candidateType, slotNormalised);
                    } catch (const TypeError&) {
                        eq = false;
                    }
                    if (eq) {
                        int deBruijnIndex =
                            static_cast<int>(localBinders.size()) - 1 - j;
                        elaboratedArgs[i] =
                            makeBoundVariable(deBruijnIndex);
                        lastDischarges_.push_back(
                            {deBruijnIndex,
                             static_cast<int>(localBinders.size()),
                             localBinders[j].name});
                        found = true;
                        break;
                    }
                }
                if (!found) remaining.push_back(i);
            }
            unresolved = std::move(remaining);
        }
        // Step 5c: match-and-unify discharge. A slot Step 5b couldn't
        // touch because its type STILL references unresolved holes — e.g.
        // `HasDegree(r, p, d)` where `r`, `p` are value holes the
        // conclusion never pinned (HasDegree_unique's conclusion is just
        // `d = e`). Try UNIFYING the slot pattern against each in-scope
        // hypothesis (local binders — which include `recalling`-bound
        // facts): a match against `HasDegree(Real.ring, modulus, d)`
        // solves `r := Real.ring`, `p := modulus` as a side effect, which
        // then lets the sibling slots discharge. The candidate set is the
        // local context only — bounded, no library search — so the user
        // having cited the lemma + recalled facts licenses the extra
        // unification effort. Iterated to a fixpoint so solved holes
        // propagate to other slots. Only runs on slots that would
        // otherwise error, so it never changes an already-resolved call.
        if (!unresolved.empty()) {
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            int N = static_cast<int>(localBinders.size());
            bool progress = true;
            while (progress && !unresolved.empty()) {
                progress = false;
                std::vector<size_t> stillUnresolved;
                for (size_t i : unresolved) {
                    // A value hole (e.g. the ring/poly of HasDegree_unique)
                    // may have been solved as a side effect of unifying a
                    // sibling proof slot. Resolve it from the assignment
                    // and drop it from the unresolved set.
                    {
                        auto solved = assignment.find(argFreshNames[i]);
                        if (solved != assignment.end()) {
                            elaboratedArgs[i] = solved->second;
                            progress = true;
                            continue;
                        }
                    }
                    ExpressionPointer slotType =
                        substituteFreeVariables(piDomains[i], assignment);
                    ExpressionPointer slotOpened;
                    try {
                        slotOpened = openOverLocalBinders(
                            slotType, localBinders, N);
                    } catch (...) {
                        stillUnresolved.push_back(i); continue;
                    }
                    // No pre-Prop gate here: the slot type still carries
                    // unresolved hole FVs (the very ones we hope to solve),
                    // so it isn't yet well-formed enough to classify. We
                    // check Prop-ness AFTER unification resolves them, which
                    // preserves "never fill a value hole from context".
                    bool filled = false;
                    for (int j = N - 1; j >= 0 && !filled; --j) {
                        ExpressionPointer candidateType =
                            openOverLocalBinders(
                                localBinders[j].type, localBinders, j);
                        // Trial-unify the slot pattern against the
                        // candidate, solving the slot's remaining holes.
                        std::map<std::string, ExpressionPointer> trial =
                            assignment;
                        std::vector<ExpressionPointer> binderStack;
                        try {
                            unifyConstructorParameters(
                                slotOpened, candidateType,
                                metavariableNames, trial, 0, &binderStack);
                        } catch (...) { continue; }
                        // Confirm the solved holes make the slot defeq the
                        // candidate (so the hypothesis really proves it).
                        ExpressionPointer slotResolved;
                        try {
                            slotResolved = openOverLocalBinders(
                                substituteFreeVariables(
                                    piDomains[i], trial),
                                localBinders, N);
                        } catch (...) { continue; }
                        bool eq;
                        try {
                            eq = isDefinitionallyEqual(
                                environment_, openedContext,
                                slotResolved, candidateType);
                        } catch (...) { eq = false; }
                        if (!eq) continue;
                        // Only ever discharge a PROOF obligation this way —
                        // never fill a value hole from a same-typed
                        // hypothesis (that must come from the goal).
                        bool resolvedIsProp = false;
                        try {
                            resolvedIsProp = typeIsProposition(
                                openedContext,
                                weakHeadNormalForm(
                                    environment_, slotResolved));
                        } catch (...) { resolvedIsProp = false; }
                        if (!resolvedIsProp) continue;
                        // Commit: adopt the newly-solved holes (closed to
                        // the global closed-over-localBinders form) and
                        // fill this slot with the hypothesis.
                        for (auto& entry : trial) {
                            if (assignment.count(entry.first)) continue;
                            ExpressionPointer closedValue;
                            try {
                                closedValue = closeOverLocalBinders(
                                    entry.second, localBinders, N);
                            } catch (...) { closedValue = entry.second; }
                            assignment[entry.first] = closedValue;
                        }
                        int deBruijnIndex = N - 1 - j;
                        elaboratedArgs[i] =
                            makeBoundVariable(deBruijnIndex);
                        lastDischarges_.push_back(
                            {deBruijnIndex, N, localBinders[j].name});
                        filled = true;
                        progress = true;
                    }
                    if (!filled) stillUnresolved.push_back(i);
                }
                unresolved = std::move(stillUnresolved);
            }
        }
        if (!unresolved.empty()) {
            std::string message =
                "call to '" + diagnosticName
                + "' at line " + std::to_string(line)
                + ": could not infer hole(s) at position";
            if (unresolved.size() > 1) message += "s";
            for (size_t p : unresolved) {
                message += " " + std::to_string(p);
            }
            if (expectedType) {
                message += "\n  expected return type: ";
                message += prettyPrintInLocalScope(
                    expectedType, localBinders);
            }
            message += "\n  Provide the missing argument(s) explicitly "
                       "to disambiguate.";
            throwElaborate(message);
        }
        return elaboratedArgs;
    }

    // Constructor-specific wrapper around `inferLeadingArguments`. Handles
    // the universe-argument plumbing and assembles the final constructor
    // application.
    ExpressionPointer elaborateConstructorCallInferringParameters(
        const Constructor& constructor,
        const Inductive& inductive,
        const std::vector<SurfaceExpressionPointer>& valueArgumentsSurface,
        const std::vector<LevelPointer>& universeArguments,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {

        ExpressionPointer constructorType = substituteUniverseLevels(
            constructor.type, constructor.universeParameters,
            universeArguments);
        CallInferenceResult inferred = inferLeadingArguments(
            constructor.inductiveName,
            constructorType,
            inductive.numParameters,
            valueArgumentsSurface,
            localBinders,
            expectedType,
            "_constructorParameter_",
            line);

        const std::string& constructorName =
            inductive.constructorNames[constructor.constructorIndex];
        ExpressionPointer head = makeConstant(constructorName,
                                               universeArguments);
        for (auto& parameterValue : inferred.leadingValues) {
            head = makeApplication(std::move(head),
                                    std::move(parameterValue));
        }
        for (auto& valueArgument : inferred.trailingValues) {
            head = makeApplication(std::move(head),
                                    std::move(valueArgument));
        }
        return head;
    }

    ExpressionPointer elaborateNumericLiteral(
        const SurfaceNumericLiteral& numeric,
        int line, int column) {
        // Desugar `25` to successor(successor(...zero)) with 25 successors.
        // Requires Natural, zero, successor to be in the environment.
        if (environment_.lookup("Natural") == nullptr
            || environment_.lookup("zero") == nullptr
            || environment_.lookup("successor") == nullptr) {
            throw ElaborateError(
                "numeric literal at line " + std::to_string(line)
                + " requires Natural, zero, and successor to be in the "
                "environment (import Natural.basics)");
        }
        int value = std::stoi(numeric.digits);
        ExpressionPointer term = makeConstant("zero");
        for (int i = 0; i < value; ++i) {
            term = makeApplication(makeConstant("successor"),
                                    std::move(term));
        }
        (void)column;
        return term;
    }

    ExpressionPointer elaboratePiType(
        const SurfacePiType& piType,
        const std::vector<LocalBinder>& localBinders) {
        if (piType.binder.names.empty()) {
            // Anonymous: T → U.
            ExpressionPointer domain =
                elaborateExpression(*piType.binder.type, localBinders);
            std::vector<LocalBinder> extended = localBinders;
            extended.push_back({"_", domain});
            ExpressionPointer codomain =
                elaborateExpression(*piType.codomain, extended);
            return makePi("_", std::move(domain), std::move(codomain));
        }
        // Multi-name binder: (x y z : T) → U becomes a chain of Pis.
        std::vector<LocalBinder> extended = localBinders;
        std::vector<ExpressionPointer> domainsPerName;
        for (const auto& name : piType.binder.names) {
            ExpressionPointer domainHere =
                elaborateExpression(*piType.binder.type, extended);
            domainsPerName.push_back(domainHere);
            extended.push_back({name, domainHere});
        }
        ExpressionPointer codomain =
            elaborateExpression(*piType.codomain, extended);
        ExpressionPointer result = codomain;
        for (int i = static_cast<int>(piType.binder.names.size()) - 1;
             i >= 0; --i) {
            result = makePi(piType.binder.names[i],
                            std::move(domainsPerName[i]),
                            std::move(result));
        }
        return result;
    }

    ExpressionPointer elaborateLambda(
        const SurfaceLambda& lambda,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType = nullptr) {
        if (lambda.binder.names.empty()) {
            throw ElaborateError("lambda binder must have at least one name");
        }
        // Pre-walk the expected Pi if present. Two things drop out:
        //   - per-name domain types (for untyped binders, used directly;
        //     for typed binders, double-checked against the annotation)
        //   - the expected body type after peeling lambda.binder.names
        //     Pi binders, for downstream constructor-parameter inference.
        std::vector<ExpressionPointer> expectedDomainsPerName;
        ExpressionPointer expectedBody = nullptr;
        if (expectedType) {
            // Force opaque heads so a `↦`-lambda body written against an
            // opaque expected type (`IsNonneg(x)`, whose unfolding is the
            // `∀ ε. ε > 0 → …` Pi) can read its binder domains — the
            // structured-construct counterpart of the kernel's retries
            // (replaces `unfold IsNonneg in ((ε)(εpos) ↦ …)`).
            ExpressionPointer cursor =
                weakHeadNormalFormForcingOpaqueHead(expectedType);
            bool ok = true;
            for (size_t k = 0; k < lambda.binder.names.size(); ++k) {
                auto* pi = std::get_if<Pi>(&cursor->node);
                if (!pi) { ok = false; break; }
                expectedDomainsPerName.push_back(pi->domain);
                cursor = weakHeadNormalFormForcingOpaqueHead(pi->codomain);
            }
            if (ok) {
                expectedBody = cursor;
            } else {
                expectedDomainsPerName.clear();
            }
        }
        std::vector<LocalBinder> extended = localBinders;
        std::vector<ExpressionPointer> domainsPerName;
        for (size_t k = 0; k < lambda.binder.names.size(); ++k) {
            const auto& name = lambda.binder.names[k];
            ExpressionPointer domainHere;
            if (lambda.binder.type) {
                domainHere =
                    elaborateExpression(*lambda.binder.type, extended);
            } else {
                // Untyped binder: read the domain from the expected
                // Pi. The kernel term is already in the right scope
                // (it came out of the Pi's domain in the surrounding
                // context); we just need to lift past the binders
                // we've added so far inside this lambda.
                if (k >= expectedDomainsPerName.size()) {
                    throw ElaborateError(
                        "lambda binder '" + name + "' has no type "
                        "annotation and no expected type to infer "
                        "from at this position");
                }
                domainHere = liftBoundVariables(
                    expectedDomainsPerName[k],
                    static_cast<int>(k), 0);
            }
            domainsPerName.push_back(domainHere);
            extended.push_back({name, domainHere});
        }
        ExpressionPointer body =
            elaborateExpression(*lambda.body, extended, expectedBody);
        // Diff-wrap the body if the expected codomain is an equality
        // and the body's type doesn't directly match. Catches
        // `function (rep) => congruenceOf(λ, P)` simplifications
        // where bare `P` would suffice given diff inference.
        if (expectedBody) {
            body = coerceToExpectedTypeViaDiff(
                extended, body, expectedBody);
            checkRedundantCongruenceOfWrapper(
                lambda.body, extended, expectedBody,
                "lambda body");
        }
        // Unused-name warning. Restricted to `suppose ... as`
        // statement-level intros — a `suppose P as h;` whose body
        // ignores `h` is almost always a refactor leftover. Function
        // lambdas (`function (x : T) (y : U) => body`) deliberately
        // do NOT trigger this warning, even when `y` goes unused —
        // C++'s `void foo(int)`-style omission isn't available in
        // this surface yet, and forcing the user to rename to `_y`
        // costs as much as just keeping `y`, so the warning would
        // produce noise without progress. Checked at the SURFACE
        // level (the user's body must textually reference the name)
        // because the elaborator may reference a binder on the
        // user's behalf — e.g. the bare-proposition-as-proof
        // coercion finds hypotheses by type, not by name.
        if (lambda.fromStatementIntro
            && lambda.binder.names.size() == 1) {
            warnIfSurfaceNameUnused(
                lambda.binder.names[0], *lambda.body,
                lambda.body->line, lambda.body->column,
                "`suppose ... as`");
        }
        ExpressionPointer result = body;
        for (int i = static_cast<int>(lambda.binder.names.size()) - 1;
             i >= 0; --i) {
            result = makeLambda(lambda.binder.names[i],
                                std::move(domainsPerName[i]),
                                std::move(result));
        }
        return result;
    }

    // -------- level elaboration --------

    // Defined out-of-line in elaborator_levels.cpp.
    LevelPointer elaborateLevel(const SurfaceLevel& level);

    // Resolves a binary arithmetic operator (`+`, `*`, ...) to a kernel
    // function call. For v1 the resolution table is hardcoded to the
    // Natural namespace: if both operands have type Natural, use
    // Natural.add / Natural.multiply. Otherwise an ElaborateError is
    // raised. A proper using-declaration-driven mechanism is the next
    // iteration.
    ExpressionPointer desugarArithmeticOperator(
        const std::string& operatorSymbol,
        const SurfaceExpression& leftSurface,
        const SurfaceExpression& rightSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {
        // First: if a local binder has the operator symbol as its
        // name (introduced via `((·) : G → G → G)`-style binders),
        // treat the operator as an application of that binder. This
        // lets group/ring theorems use `x · y` for the bound
        // operation without having to plumb it through the global
        // operator registry.
        for (size_t i = localBinders.size(); i > 0; --i) {
            if (localBinders[i - 1].name == operatorSymbol) {
                ExpressionPointer leftLocal =
                    elaborateExpression(leftSurface, localBinders);
                ExpressionPointer rightLocal =
                    elaborateExpression(rightSurface, localBinders);
                ExpressionPointer functionExpression =
                    elaborateIdentifier(
                        SurfaceIdentifier{operatorSymbol, {}},
                        localBinders, line, /*column=*/0);
                ExpressionPointer call = makeApplication(
                    std::move(functionExpression), std::move(leftLocal));
                call = makeApplication(std::move(call),
                                        std::move(rightLocal));
                return call;
            }
        }
        // `≥` and `>` desugar to the flipped `≤`/`<` against the same
        // carrier. We never register a separate function for them — the
        // existing `≤`/`<` registry entries are reused with the operand
        // order reversed. This keeps a single source of truth for the
        // order relation and lets calc chains mix the two notations.
        if (operatorSymbol == "≥") {
            return desugarArithmeticOperator(
                "≤", rightSurface, leftSurface, localBinders,
                expectedType, line);
        }
        if (operatorSymbol == ">") {
            return desugarArithmeticOperator(
                "<", rightSurface, leftSurface, localBinders,
                expectedType, line);
        }
        // Logical operators are dispatched first because their operand
        // type is a Proposition (a `Sort`, not a `Constant`), so the
        // numeric-operator dispatch below — which looks for a Constant
        // head on the inferred operand type — wouldn't see them.
        std::string logicalTarget;
        if (operatorSymbol == "∧") logicalTarget = "And";
        else if (operatorSymbol == "∨") logicalTarget = "Or";
        if (!logicalTarget.empty()) {
            if (environment_.lookup(logicalTarget) == nullptr) {
                throw ElaborateError(
                    "operator '" + operatorSymbol + "' resolves to '"
                    + logicalTarget + "' but that inductive is not in "
                    "scope (line " + std::to_string(line)
                    + "); import Logic.basics");
            }
            ExpressionPointer leftLogical =
                elaborateExpression(leftSurface, localBinders);
            ExpressionPointer rightLogical =
                elaborateExpression(rightSurface, localBinders);
            ExpressionPointer call = makeConstant(logicalTarget);
            call = makeApplication(std::move(call), std::move(leftLogical));
            call = makeApplication(std::move(call), std::move(rightLogical));
            return call;
        }
        // Use the outer expected type as a hint for the LEFT operand
        // only when it's a Constant head — e.g. `Rational`, `Integer`,
        // `Real`, `PAdic`. For arithmetic operators like `+`, `*`,
        // `-`, the result type equals the operand type, so the hint
        // is exactly the operand type. For `≤`, `<`, etc. the result
        // type is `Proposition` (a Sort, not a Constant), so the
        // guard skips them. Lets short-form `Quotient.mk(rep)` fire
        // on the LEFT of a homogeneous operator when the outer
        // context provides the carrier head.
        ExpressionPointer leftExpectedType = nullptr;
        if (expectedType
            && std::holds_alternative<Constant>(expectedType->node)) {
            leftExpectedType = expectedType;
        }
        ExpressionPointer leftKernel =
            elaborateExpression(leftSurface, localBinders,
                                 leftExpectedType);
        // Determine the operand type by inferring the type of the left
        // operand. Check the raw inferred type first: if a binder was
        // declared with a named type like `Integer` (which δ-reduces
        // to `Quotient(IntegerRepresentative, IntegerEquivalent)`),
        // we want to dispatch on `Integer`, not the unfolded form.
        // Only WHNF as a fallback for types that are themselves
        // computations (rare in practice but used by let-bindings
        // whose type-annotation is a reducible expression).
        ExpressionPointer leftTypeRaw =
            inferTypeInLocalContext(localBinders, leftKernel);
        // Propagate the left operand's type as expected type for the
        // right operand. This lets short-form `Quotient.mk(rep)` (with
        // R inferred from expected type) fire in operand position of
        // homogeneous operators like `+`, `*`, `≤`, `<` on Rational,
        // Real, etc. — mirrors the `=` desugaring's identical trick.
        ExpressionPointer leftTypeClosed = closeOverLocalBinders(
            leftTypeRaw, localBinders, localBinders.size());
        ExpressionPointer rightKernel =
            elaborateExpression(rightSurface, localBinders,
                                 leftTypeClosed);
        // Use `headConstantName` to extract the type head — peels through
        // Applications so parameterised types like `Set(T)` report `Set`
        // and `Quotient(IR, IE)` reports `Quotient`. Falls back to WHNF
        // for definitional aliases whose RHS exposes a different head.
        std::string operandTypeName = headConstantName(leftTypeRaw);
        std::string targetFunction;
        // First consult the user-declared registry: any
        // `operator (sym) on (T1, T2) := F;` registration wins. This is
        // the extensible path — Rational, Real, Complex, polynomial
        // rings, etc. all hook in here. Wildcard `_` registrations
        // (e.g. `∈` on `(_, Set)`) match any LHS or RHS type.
        ExpressionPointer rightTypeRaw =
            inferTypeInLocalContext(localBinders, rightKernel);
        std::string rightTypeName = headConstantName(rightTypeRaw);
        std::string registered = environment_.lookupOperator(
            operatorSymbol, operandTypeName, rightTypeName);
        if (!registered.empty()) {
            targetFunction = registered;
        }
        // Fallback: if the raw head Constant didn't match anything,
        // try operand-type names from the registry whose definition
        // δ-reduces to the operand's actual type. This catches
        // `Quotient.mk(IntegerRepresentative, IntegerEquivalent, _)`
        // (raw type head: `Quotient`) being treated as `Integer`
        // (whose definition body is exactly that `Quotient(...)`).
        if (targetFunction.empty()) {
            ExpressionPointer operandLeftWHNF = weakHeadNormalForm(
                environment_, leftTypeRaw);
            ExpressionPointer operandRightWHNF = weakHeadNormalForm(
                environment_, rightTypeRaw);
            for (const auto& [key, funcName]
                 : environment_.operatorRegistry) {
                const auto& [opSym, leftReg, rightReg] = key;
                if (opSym != operatorSymbol) continue;
                const Declaration* leftDecl =
                    environment_.lookup(leftReg);
                const Declaration* rightDecl =
                    environment_.lookup(rightReg);
                auto* leftDef = leftDecl
                    ? std::get_if<Definition>(leftDecl) : nullptr;
                auto* rightDef = rightDecl
                    ? std::get_if<Definition>(rightDecl) : nullptr;
                if (!leftDef || !rightDef) continue;
                ExpressionPointer leftRegBodyWHNF = weakHeadNormalForm(
                    environment_, leftDef->body);
                ExpressionPointer rightRegBodyWHNF = weakHeadNormalForm(
                    environment_, rightDef->body);
                if (structurallyEqual(leftRegBodyWHNF, operandLeftWHNF)
                    && structurallyEqual(rightRegBodyWHNF,
                                            operandRightWHNF)) {
                    targetFunction = funcName;
                    break;
                }
            }
        }
        // Final registry fallback: WHNF the operand types to expose a
        // CONCRETE carrier head. A value whose type is a bundle projection
        // over a concrete ring — `Ring.carrier(Real.polynomial_ring)` (from
        // a `divides` existential), or `Ring.carrier(Real.ring)` — reduces
        // to the concrete carrier (`Polynomial(...)`, `Real`), so it then
        // dispatches like that concrete type. An ABSTRACT carrier
        // (`Ring.carrier(s)` for a variable `s`) stays stuck under WHNF, so
        // its bundle dispatch is unchanged. Only consulted after the
        // raw-head lookup failed, so this never overrides an existing
        // dispatch — it can only turn a previously-erroring mixed/projected
        // head pair into a successful one.
        if (targetFunction.empty()) {
            // Resolve a carrier PROJECTION over a concrete ring to the
            // carrier field as written in the bundle's constructor (NOT
            // further reduced — full WHNF would blow past `Polynomial(…)`
            // to its underlying `Quotient(…)`). So a value typed
            // `Ring.carrier(Real.polynomial_ring)` (from a `divides`
            // existential) dispatches like `Polynomial`. An abstract
            // `Ring.carrier(s)` resolves to nothing (the bundle arg is
            // stuck), so its dispatch is unchanged.
            ExpressionPointer leftProj =
                carrierProjectionField(leftTypeRaw);
            ExpressionPointer rightProj =
                carrierProjectionField(rightTypeRaw);
            std::string leftProjHead =
                leftProj ? headConstantName(leftProj) : std::string();
            std::string rightProjHead =
                rightProj ? headConstantName(rightProj) : std::string();
            const std::string leftCandidates[2] =
                {leftProjHead, operandTypeName};
            const std::string rightCandidates[2] =
                {rightProjHead, rightTypeName};
            for (int li = 0; li < 2 && targetFunction.empty(); ++li) {
                for (int ri = 0; ri < 2 && targetFunction.empty(); ++ri) {
                    if (li == 1 && ri == 1) continue;  // raw×raw already tried
                    if (leftCandidates[li].empty()
                        || rightCandidates[ri].empty()) continue;
                    std::string reg = environment_.lookupOperator(
                        operatorSymbol, leftCandidates[li],
                        rightCandidates[ri]);
                    if (!reg.empty()) targetFunction = reg;
                }
            }
        }
        // For `<` we wrap the left operand in `successor`, since
        // `a < b` is defined as `LessOrEqual(successor(a), b)`. This is
        // special enough that we leave it built-in.
        bool wrapLeftInSuccessor = false;
        if (targetFunction.empty()) {
            if (operandTypeName == "Natural") {
                if (operatorSymbol == "≤") targetFunction = "LessOrEqual";
                else if (operatorSymbol == "<") {
                    targetFunction = "LessOrEqual";
                    wrapLeftInSuccessor = true;
                }
                else if (operatorSymbol == "∣") targetFunction = "Natural.divides";
            }
        }
        if (targetFunction.empty()) {
            throw ElaborateError(
                "operator '" + operatorSymbol + "' is not supported for "
                "operand type '" + operandTypeName + "' (line "
                + std::to_string(line)
                + "); supported: +, *, ≤, <, ∣ on Natural; +, *, - on "
                "Integer; ∧, ∨ on Proposition");
        }
        if (environment_.lookup(targetFunction) == nullptr) {
            throw ElaborateError(
                "operator '" + operatorSymbol + "' resolves to '"
                + targetFunction + "' but that function is not in scope "
                "(line " + std::to_string(line) + ")");
        }
        if (wrapLeftInSuccessor) {
            if (environment_.lookup("successor") == nullptr) {
                throw ElaborateError(
                    "operator '<' on Natural requires `successor` in scope "
                    "(line " + std::to_string(line) + ")");
            }
            leftKernel = makeApplication(
                makeConstant("successor"), std::move(leftKernel));
        }
        ExpressionPointer call = makeConstant(targetFunction);
        // Fill any leading implicit binders the dispatch function may
        // have. Two patterns are common:
        //   (a) `Set.member {T : Type(0)} (x : T) (S : Set(T))` —
        //       the implicit carrier is the LEFT operand's type T.
        //   (b) `Set.subset {T : Type(0)} (A : Set(T)) (B : Set(T))` —
        //       the implicit carrier is the *parameter* of the LEFT
        //       operand's type `Set(T)`, not `Set(T)` itself.
        // We recover the fillers by unifying the LEFT operand's type
        // against the target function's first-explicit-argument type
        // template (which has BoundVariable references to the implicit
        // binders). Works for both patterns above and any
        // structurally-decomposable shape — in particular, it doesn't
        // trip when the LEFT operand's type is itself a parameterised
        // alias like `Real = Quotient(_, _)`.
        int implicitCount =
            environment_.implicitArgumentCount(targetFunction);
        if (implicitCount > 0) {
            std::vector<ExpressionPointer> implicitBindings(implicitCount);
            bool inferredByUnification = false;
            if (const Declaration* targetDecl =
                    environment_.lookup(targetFunction)) {
                ExpressionPointer cursor = declarationType(*targetDecl);
                for (int i = 0; i < implicitCount && cursor; ++i) {
                    auto* pi = std::get_if<Pi>(&cursor->node);
                    if (!pi) { cursor = nullptr; break; }
                    cursor = pi->codomain;
                }
                if (cursor) {
                    if (auto* firstExplicit =
                            std::get_if<Pi>(&cursor->node)) {
                        if (matchAgainstPattern(
                                firstExplicit->domain, leftTypeClosed,
                                implicitCount, implicitBindings)) {
                            inferredByUnification = true;
                            for (const auto& binding : implicitBindings) {
                                if (!binding) {
                                    inferredByUnification = false;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            if (inferredByUnification) {
                // bindings[0] is the INNERMOST implicit (smallest BV
                // index from inside). Application order is outermost-
                // first, so apply in reverse.
                for (int i = implicitCount - 1; i >= 0; --i) {
                    call = makeApplication(std::move(call),
                                             implicitBindings[i]);
                }
            } else {
                // Fall back to the legacy single-filler heuristic for
                // safety. If this fires, the kernel typecheck will
                // catch a mismatch — better than silently building a
                // wrong term, no worse than the prior behaviour.
                ExpressionPointer implicitFiller = leftTypeClosed;
                auto* leftTypeApp =
                    std::get_if<Application>(&leftTypeClosed->node);
                if (leftTypeApp) {
                    implicitFiller = leftTypeApp->argument;
                }
                for (int i = 0; i < implicitCount; ++i) {
                    call = makeApplication(std::move(call),
                                             implicitFiller);
                }
            }
        }
        call = makeApplication(std::move(call), std::move(leftKernel));
        call = makeApplication(std::move(call), std::move(rightKernel));
        return call;
    }

    // Desugars `reflexivity(subject)` into
    // `reflexivity.{u}(typeOfSubject, subject)` where u is the subject's
    // type universe. Mirrors how the constructor's signature makes the
    // carrier type and its universe inferable from the subject.
    ExpressionPointer desugarReflexivity(
        SurfaceExpressionPointer subjectSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {
        ExpressionPointer subjectKernel =
            elaborateExpression(*subjectSurface, localBinders);
        ExpressionPointer subjectTypeOpened =
            inferTypeInLocalContext(localBinders, subjectKernel);
        ExpressionPointer subjectType = closeOverLocalBinders(
            subjectTypeOpened, localBinders, localBinders.size());
        LevelPointer carrierUniverseLevel =
            typeUniverseOf(localBinders, subjectKernel);
        ExpressionPointer call =
            makeConstant("reflexivity", {carrierUniverseLevel});
        call = makeApplication(std::move(call), std::move(subjectType));
        call = makeApplication(std::move(call), std::move(subjectKernel));
        (void)line; (void)column;
        return call;
    }

    // Helper: given a kernel term whose type (already weak-head-normalised)
    // is `Equality.{u}(A, x, y)`, extracts the four components. Throws
    // ElaborateError if the type doesn't have that shape.
    struct EqualityComponents {
        ExpressionPointer carrierType;
        ExpressionPointer leftEndpoint;
        ExpressionPointer rightEndpoint;
        LevelPointer carrierUniverseLevel;
    };
    EqualityComponents extractEqualityComponents(
        ExpressionPointer equalityType, const char* contextLabel,
        int line) {
        // WHNF the type so a β-redex (e.g. the predicate body of an
        // Exists destructured via `obtain ⟨k, eq⟩` — the binder's
        // type starts as `(λ k'. P k')(k)`) reduces to the
        // applied-`Equality.{u}` form we expect to destructure below.
        equalityType =
            weakHeadNormalForm(environment_, equalityType);
        auto* outerApp = std::get_if<Application>(&equalityType->node);
        if (!outerApp) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type is not a fully applied Equality "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer rightEndpoint = outerApp->argument;
        auto* middleApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!middleApp) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type is not a fully applied Equality "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer leftEndpoint = middleApp->argument;
        auto* innerApp =
            std::get_if<Application>(&middleApp->function->node);
        if (!innerApp) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type is not a fully applied Equality "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer carrierType = innerApp->argument;
        auto* equalityConstant =
            std::get_if<Constant>(&innerApp->function->node);
        if (!equalityConstant
            || equalityConstant->name != "Equality"
            || equalityConstant->universeArguments.size() != 1) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type isn't an Equality.{u} (line "
                + std::to_string(line) + ")");
        }
        return {carrierType, leftEndpoint, rightEndpoint,
                equalityConstant->universeArguments[0]};
    }

    // Desugars `Equality.symmetry(equalityProof)` to the full call with
    // the carrier type and endpoint values inferred from the proof's
    // type.
    ExpressionPointer desugarEqualitySymmetry(
        SurfaceExpressionPointer equalityProofSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {
        ExpressionPointer equalityProofKernel =
            elaborateExpression(*equalityProofSurface, localBinders);
        ExpressionPointer equalityProofType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          equalityProofKernel));
        EqualityComponents components = extractEqualityComponents(
            equalityProofType, "Equality.symmetry", line);
        ExpressionPointer carrierType = closeOverLocalBinders(
            components.carrierType, localBinders, localBinders.size());
        ExpressionPointer leftEndpoint = closeOverLocalBinders(
            components.leftEndpoint, localBinders, localBinders.size());
        ExpressionPointer rightEndpoint = closeOverLocalBinders(
            components.rightEndpoint, localBinders, localBinders.size());
        ExpressionPointer call =
            makeConstant("Equality.symmetry",
                          {components.carrierUniverseLevel});
        call = makeApplication(std::move(call), std::move(carrierType));
        call = makeApplication(std::move(call), std::move(leftEndpoint));
        call = makeApplication(std::move(call), std::move(rightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(equalityProofKernel));
        (void)column;
        return call;
    }

    // Desugars `Equality.transitivity(firstEquality, secondEquality)`
    // to the full call, with the carrier type and the three endpoints
    // inferred from the two argument equalities' types.
    ExpressionPointer desugarEqualityTransitivity(
        SurfaceExpressionPointer firstEqualitySurface,
        SurfaceExpressionPointer secondEqualitySurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        // If the surrounding context provided an expected type
        // `Equality(carrier, A, C)`, synthesize `Equality(carrier, A, A)`
        // as the expected type for the first argument so that desugars
        // like rewrite (which need an expected type) can fire there too.
        // Otherwise the first argument elaborates without an expected
        // type, exactly as before.
        ExpressionPointer expectedForFirst;
        if (expectedType) {
            ExpressionPointer expectedOpened = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            ExpressionPointer expectedWhnf = weakHeadNormalForm(
                environment_, expectedOpened);
            EqualityComponents outerComponents;
            try {
                outerComponents = extractEqualityComponents(
                    expectedWhnf,
                    "Equality.transitivity (outer expected)", line);
                ExpressionPointer outerCarrier = closeOverLocalBinders(
                    outerComponents.carrierType,
                    localBinders, localBinders.size());
                ExpressionPointer outerLeft = closeOverLocalBinders(
                    outerComponents.leftEndpoint,
                    localBinders, localBinders.size());
                expectedForFirst = makeConstant(
                    "Equality",
                    {outerComponents.carrierUniverseLevel});
                expectedForFirst = makeApplication(
                    std::move(expectedForFirst), outerCarrier);
                expectedForFirst = makeApplication(
                    std::move(expectedForFirst), outerLeft);
                expectedForFirst = makeApplication(
                    std::move(expectedForFirst), outerLeft);
            } catch (const ElaborateError&) {
                // Outer expected type isn't an Equality — proceed
                // without synthesizing.
            }
        }
        ExpressionPointer firstEqualityKernel =
            elaborateExpression(*firstEqualitySurface, localBinders,
                                  expectedForFirst);
        ExpressionPointer firstEqualityType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          firstEqualityKernel));
        EqualityComponents firstComponents = extractEqualityComponents(
            firstEqualityType,
            "Equality.transitivity (first argument)", line);
        // Build the closed-over endpoints early so we can compose a
        // synthetic expected type for the second argument.
        ExpressionPointer carrierTypeForExpected =
            closeOverLocalBinders(firstComponents.carrierType,
                                    localBinders, localBinders.size());
        ExpressionPointer middleForExpected =
            closeOverLocalBinders(firstComponents.rightEndpoint,
                                    localBinders, localBinders.size());
        ExpressionPointer expectedForSecond = makeConstant(
            "Equality",
            {firstComponents.carrierUniverseLevel});
        expectedForSecond = makeApplication(
            std::move(expectedForSecond), carrierTypeForExpected);
        expectedForSecond = makeApplication(
            std::move(expectedForSecond), middleForExpected);
        expectedForSecond = makeApplication(
            std::move(expectedForSecond), middleForExpected);
        ExpressionPointer secondEqualityKernel =
            elaborateExpression(*secondEqualitySurface, localBinders,
                                  expectedForSecond);
        ExpressionPointer secondEqualityType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          secondEqualityKernel));
        EqualityComponents secondComponents = extractEqualityComponents(
            secondEqualityType,
            "Equality.transitivity (second argument)", line);
        ExpressionPointer carrierType = closeOverLocalBinders(
            firstComponents.carrierType,
            localBinders, localBinders.size());
        ExpressionPointer leftEndpoint = closeOverLocalBinders(
            firstComponents.leftEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer middleEndpoint = closeOverLocalBinders(
            firstComponents.rightEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer rightEndpoint = closeOverLocalBinders(
            secondComponents.rightEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer call = makeConstant(
            "Equality.transitivity",
            {firstComponents.carrierUniverseLevel});
        call = makeApplication(std::move(call), std::move(carrierType));
        call = makeApplication(std::move(call), std::move(leftEndpoint));
        call = makeApplication(std::move(call),
                                std::move(middleEndpoint));
        call = makeApplication(std::move(call), std::move(rightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(firstEqualityKernel));
        call = makeApplication(std::move(call),
                                std::move(secondEqualityKernel));
        (void)column;
        return call;
    }

    // Desugars `congruenceOf(f, h)` into a full call to
    // `Equality.congruence.{u, v}(A, B, f, x, y, h)` by inferring the
    // type arguments and universes from the kernel types of f and h.
    // Requires `Equality.congruence` to be in the environment.
    // Walks `expression` looking for subterms structurally equal to
    // `target`. Each match is replaced by `BoundVariable(currentDepth)`,
    // and every other BoundVariable referring to outer scope is shifted
    // up by 1 — preparing the result to be the body of a new outer
    // Lambda binder. Counts matches so the caller can require exactly
    // one. `target` is shifted as we descend into binders so structural
    // comparison stays correct.

    // Recursive WHNF through Application spines. WHNFs the current
    // expression, then — if the result is an Application — recursively
    // normalizes its function and argument. This exposes structural
    // shape that plain `weakHeadNormalForm` leaves alone (it only
    // reduces the outermost head). Used by `claim by substituting`'s
    // search as a fallback when the surface goal has no occurrences
    // of the equation's endpoint, but a deeper reduction would expose
    // one — e.g. under `unfold X in body`, where `X(args)` in the
    // surface goal δ-unfolds to a `cases scrutinee { … }` body whose
    // scrutinee is the substitution target.
    ExpressionPointer deepWhnfThroughApplications(
        ExpressionPointer expression);

    // True if `expression` syntactically mentions any opaque Definition
    // (a Constant whose name resolves to one), reduction-free. Gates the
    // force-unfolding substitution form so ordinary goals skip it entirely.
    bool mentionsOpaqueDefinition(const ExpressionPointer& expression);

    // The opaque-headed application at the WHNF of `expression`, or nullptr.
    // (Peels the spine and checks whether the head names an opaque Definition.)
    const Definition* opaqueHeadDefinition(const ExpressionPointer& whnfed,
                                           const Constant** outConstant);

    // WHNF that additionally δ-unfolds opaque definitions remaining at the
    // HEAD (only the head, not recursively into arguments). Exposes the true
    // head shape — a Pi, or an inductive like `Exists` — when it is hidden
    // behind an opaque wrapper (`IsNonneg(x)` → `Quotient.lift …` → `Exists`).
    // Used where the elaborator genuinely demands the unfolded head to build
    // or destructure a value (anonymous tuple against an opaque expected type),
    // mirroring the kernel's opacity-tolerant inferType/defeq retries.
    ExpressionPointer weakHeadNormalFormForcingOpaqueHead(
            ExpressionPointer expression, int fuel = 64);

    // Like deepWhnfThroughApplications, but also δ-unfolds an opaque
    // definition that remains at a head after WHNF — manually, by splicing in
    // its body, so no global opacity flip and no leak past this call. A
    // SEARCH-ONLY fallback for `claim by substituting`: the substitution
    // target can be buried inside an opaque definition's body (e.g.
    // `divide_step`'s `cases monus(p, n) {…}`), which opacity-respecting WHNF
    // never exposes. The rewritten goal this helps build is re-checked by the
    // kernel's own opacity-tolerant defeq bridge, so opacity is restored for
    // every downstream consumer.
    ExpressionPointer deepWhnfForcingOpaque(
            ExpressionPointer expression,
            const std::set<std::string>& protectedDefinitions,
            int fuel = 64);

    // Deep beta-only reduction: rewrites every (λx. body)(arg) redex
    // anywhere in the expression — never δ-unfolds Constants, so
    // user-visible names stay intact. Used as a fallback combo by
    // `rewrite(eq, term)` to catch redexes hiding inside the term's
    // type — e.g. `sequenceFunction(λn. …, m)` from Quotient.lift
    // bodies in real-analysis proofs, where the user's stated motive
    // sees the β-reduced form but the inferred type doesn't.
    ExpressionPointer deepBetaReduce(ExpressionPointer expression);

    // Abstract every occurrence of `target` in `expression`, like
    // `abstractStructuralOccurrence`, but WHNF the expression at each
    // recursion level first. This exposes target subterms (like
    // `Logic.classical_decidable(P)`) that are hidden behind a chain
    // of δ-unfoldings in the goal — e.g., `bisectionRight(…, succ(n))`
    // → `right(bisectionIntervals(…, succ(n)))` → `right(bisectionStep(…))`
    // → `right(bisectionStepWithDec(…, classical_decidable(…)))`.
    //
    // Each level WHNFs only the head, so we don't pay for fully
    // normalising the goal up front (which would expand bisection
    // proofs to unmanageable sizes). When recursion passes through a
    // binder, the BoundVariable depth advances; references to the
    // freshly introduced motive binder (BV(currentDepth)) shift their
    // free occurrences upward to leave room, mirroring
    // `abstractStructuralOccurrence`.
    //
    // WHNF failures (fuel exhaustion, etc.) leave that subterm in its
    // current form and continue.
    // Recursively replace every reference to a let-binder in
    // `expression` with the binder's value. Used by `decide` so the
    // user's proposition (which references in-scope `let X := V`
    // bindings symbolically) lines up with the goal's structure, which
    // typically predates the let-bindings and has V inlined.

    // Return the head constant name of an Application chain, or empty
    // string if the head isn't a Constant. `f(a, b, c)` returns "f".

    // Does `expression` syntactically reference `targetHeadName` as a
    // Constant somewhere? Used to seed unfoldExposesHead.
    bool expressionReferencesConstant(
        ExpressionPointer expression,
        const std::string& targetHeadName,
        std::unordered_set<std::string>& visiting);

    // Does WHNF-unfolding `constantName` produce a term that
    // syntactically (transitively, through other transparent
    // definitions) references `targetHeadName`? Memoised: each
    // constant is walked once per target. Used by the `decide` walker
    // to skip Applications whose head is provably irrelevant
    // (Real.LessOrEqual, Set.member, etc., when the target is
    // Logic.classical_decidable).
    //
    // The `visiting` set guards against cycles in mutually recursive
    // definitions — a constant currently being computed contributes
    // `false` to its own caller to avoid an infinite loop; the cached
    // result then reflects only what was reachable WITHOUT the cycle.
    bool unfoldExposesHead(
        const std::string& constantName,
        const std::string& targetHeadName,
        std::unordered_set<std::string>& visiting);

    ExpressionPointer abstractStructuralOccurrenceWithWHNF(
        ExpressionPointer expression,
        ExpressionPointer target,
        const std::string& targetHeadName,
        int currentDepth,
        int& occurrenceCount,
        int& whnfFuel);

    // Inner implementation. The wrapper above handles depth-0
    // memoization; this function does the actual work.
    ExpressionPointer abstractStructuralOccurrenceWithWHNF_inner(
        ExpressionPointer expression,
        ExpressionPointer target,
        const std::string& targetHeadName,
        int currentDepth,
        int& occurrenceCount,
        int& whnfFuel);

    // Variant of `abstractStructuralOccurrence` that abstracts a
    // SUBSET of matching occurrences, selected by index (left-to-right
    // in-order). `positionCounter` is the running counter (in/out);
    // each match increments it; the match at index i gets abstracted
    // iff `mask & (1u << i)` is set. Unselected matches stay as the
    // original expression. Used by the multi-occurrence rewrite path
    // (when the expected type is known and disambiguates which subset
    // of positions the user wants substituted).


    // Like `abstractStructuralOccurrence`, but also abstracts a subterm
    // that is only DEFINITIONALLY (not structurally) equal to `target`.
    // The last-resort matcher for `rewrite`: it locates an endpoint that
    // the structural combos miss because it is present only up to
    // definitional equality — e.g. a structure projection on a concrete
    // bundle, `Ring.multiply(Polynomial.ring(r), x, y)`, against the
    // term's spelling `Polynomial.multiply(r, x, y)`. To stay cheap it
    // calls the kernel's `isDefinitionallyEqual` only at Application
    // subterms whose spine arity equals the target's, and at most
    // `defeqBudget` times overall; a structural match is always taken
    // first (free), and a defeq match abstracts the subterm whole.
    ExpressionPointer abstractDefeqOccurrence(
        ExpressionPointer expression,
        ExpressionPointer target,
        int targetArity,
        int currentDepth,
        int& occurrenceCount,
        int& defeqBudget);

    // `rewrite(lemma)` where `lemma : Equality.{u}(T', x, y)` and the
    // current goal is `Equality.{v}(T, A, B)`: builds the proof
    //   `Equality.congruence.{u, v}(T', T, λ z ⇒ A[z/x], x, y, lemma)`
    // — locating the unique structural occurrence of `x` inside `A` and
    // replacing it with the binder of an inserted Lambda. Errors if `x`
    // doesn't appear or appears more than once (the user would have to
    // disambiguate via explicit `congruenceOf`).
    // `rewrite(equalityProof, term)` — term-level form. Given
    // `equalityProof : Equality(A, x, y)` and `term : P(x)` for some
    // Proposition-valued `P`, returns a term of type `P(y)`. Implemented
    // as `Equality.transport_proposition(A, λz. P[x↦z], x, y,
    // equalityProof, term)`. The motive is recovered by locating the
    // unique structural occurrence of `x` in `term`'s inferred type and
    // abstracting it.
    //
    // Distinguished from the 1-arg `rewrite(equalityProof)` (calc-step
    // form) by argument count. The two have different return types and
    // operate in different positions: term-level transport produces a
    // proof witness; calc-step rewrite produces an equality between two
    // calc endpoints.
    ExpressionPointer desugarRewriteTerm(
        SurfaceExpressionPointer equalityProofSurface,
        SurfaceExpressionPointer termSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    ExpressionPointer desugarRewrite(
        SurfaceExpressionPointer lemmaSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // ---- simplify --------------------------------------------------------
    //
    // `simplify(L1, L2, …, Ln)` in calc context: discharges the current
    // step's `a = b` by repeatedly rewriting `a` (or arbitrary subterms of
    // it) using any of the supplied lemmas, until the resulting term is
    // definitionally equal to `b`. Each lemma is a polymorphic equality:
    // `(p1 : T1) → … → (pk : Tk) → Equality.{u}(C, LHS, RHS)`. simplify
    // picks the first subterm of the current term that any lemma's LHS
    // pattern unifies with (Pi binders treated as metavariables), then
    // applies that lemma's RHS at the matched site via `Equality.congruence`
    // — same shape as `rewrite(L)` but with the lemma instantiated
    // automatically.
    //
    // V1 limitations:
    //   * Pattern matching is first-order: linear, no higher-order vars,
    //     no descent under binders. The lemma's LHS may not itself contain
    //     a Lambda/Pi/Let; the search through the goal also does not enter
    //     binders.
    //   * Only forward direction (LHS → RHS). The user must pass a
    //     symmetric lemma if they need a reverse rewrite.
    //   * Termination is bounded by a fixed iteration limit; non-confluent
    //     rule sets (e.g. naked commutativity) can hit the bound.

    // First-order match. `pattern` lives in a scope with `numPatternBinders`
    // leading Pi binders (the lemma's universal quantifiers); pattern uses
    // BoundVariable(0..numPatternBinders-1) to refer to them. Higher-indexed
    // BoundVariables refer to scope above the lemma's type — for a
    // top-level lemma these don't occur.
    //
    // On success, `bindings[i]` is the term substituted for the i-th
    // pattern binder. Bindings are populated as the match descends; if a
    // metavariable appears twice in the pattern, the second occurrence is
    // required to match the term already recorded (linearity).
    bool tryFirstOrderMatch(
        ExpressionPointer pattern,
        ExpressionPointer term,
        int numPatternBinders,
        std::vector<ExpressionPointer>& bindings);

    // Substitute the pattern's metavariables with their matched
    // expressions. `pattern` may reference Bound(0..numPatternBinders-1)
    // (substituted) and Bound(k >= numPatternBinders) (shifted down by
    // numPatternBinders to refer to the surrounding outer scope).
    ExpressionPointer instantiatePattern(
        ExpressionPointer pattern,
        const std::vector<ExpressionPointer>& bindings,
        int numPatternBinders,
        int currentDepth = 0);

    // A prepared simplify lemma: its kernel-level reference plus the
    // shape data needed to match-and-apply.
    struct SimplifyLemma {
        ExpressionPointer lemmaReference;     // kernel value: the lemma
        int numBinders;                        // count of universal Pis
        std::vector<ExpressionPointer> binderTypes;  // domain of each Pi
        ExpressionPointer carrier;             // T in Equality.{u}(T, …, …)
        ExpressionPointer leftPattern;         // LHS, Bound(0..n-1) = metas
        ExpressionPointer rightPattern;        // RHS, same convention
        LevelPointer carrierUniverseLevel;
    };

    // Walk `term` looking for the first subterm (Application spine,
    // leaving binders alone) where any lemma's LHS pattern matches. On
    // success, returns the lemma's index and populates `bindings`. The
    // returned `matchedSubterm` is the subterm where the match landed.
    bool findFirstSimplifyMatch(
        ExpressionPointer term,
        const std::vector<SimplifyLemma>& lemmas,
        size_t& matchedLemmaIndex,
        std::vector<ExpressionPointer>& bindings,
        ExpressionPointer& matchedSubterm);

    // Prepare the kernel-level proof witness for one rewrite step.
    // `goalCarrier` is the carrier of the calc step's equality; `current`
    // is the term we're rewriting (LHS of the residual `current = target`
    // step); `newCurrent` is the result after this rewrite. The returned
    // expression has type `Equality.{v}(goalCarrier, current, newCurrent)`.
    ExpressionPointer buildSingleSimplifyStep(
        const SimplifyLemma& lemma,
        const std::vector<ExpressionPointer>& bindings,
        ExpressionPointer current,
        ExpressionPointer matchedSubterm,
        ExpressionPointer newCurrent,
        ExpressionPointer goalCarrier,
        LevelPointer goalCarrierUniverseLevel,
        ExpressionPointer instantiatedRight);

    ExpressionPointer desugarSimplify(
        const std::vector<SurfaceExpressionPointer>& lemmaSurfaces,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // ---- absurd ---------------------------------------------------------
    //
    // `absurd(witness)` — discharges any goal from a contradictory
    // witness. Recognized shapes for `witness`'s type:
    //   * `False`                                  — used directly.
    //   * `successor(K) ≤ zero`                    — applies
    //                                                Natural.not_less_or_equal_successor_zero.
    //   * `successor(K) = zero` / `zero = successor(K)` — applies
    //                                                Natural.successor_not_zero /
    //                                                Natural.zero_not_successor.
    // Then emits `False.eliminate_proposition(GOAL, falseProof)` where
    // GOAL comes from the expected type at the call site. Adding more
    // shapes is mechanical — register the pattern + matching lemma name
    // below.
    ExpressionPointer desugarAbsurd(
        SurfaceExpressionPointer witnessSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // Pick the unique overload candidate that matches the user-supplied
    // argument types. Errors if zero or multiple candidates match.
    // Matching is by Constant-head name of each parameter type (raw,
    // not WHNF'd — so a parameter declared as `Rational` matches an
    // argument of type `Rational` even though Rational δ-reduces to
    // `Quotient(...)`. WHNF is used as a fallback when the raw form
    // isn't a Constant.) Partial application of an overloaded name is
    // not supported: if `f` has only 2-ary overloads, `f(p)` is an
    // error — wrap in `function (q) => f(p, q)` instead.
    ExpressionPointer resolveOverloadedCall(
        const std::string& aliasName,
        const std::vector<std::string>& candidateNames,
        const std::vector<SurfaceExpressionPointer>& argumentSurfaces,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column);

    // Extract a Constant head name from a type expression. Tries the
    // raw form first (so user-declared type aliases like `Rational`
    // don't get unfolded), falls back to WHNF.
    // True if `name` is a STRUCTURE CLASS — a Definition whose first
    // parameter is a carrier TYPE (its domain is a Sort) and whose final
    // codomain is `Proposition` (Sort 0). This is what `IsGroup` / `IsRing`
    // / `IsField` look like. Used to gate instance resolution so it fires
    // ONLY on genuine instance-style arguments: it excludes data implicits
    // (`{T : Type(0)}`, `{x : Tagged(m)}`, whose head isn't even a
    // Proposition) AND ordinary value predicates like `Natural.is_prime`
    // or `Natural.divides`, whose first parameter is a value, not a
    // carrier type — those are threaded explicitly and must NOT be grabbed
    // from an in-scope hypothesis.
    bool structureHeadIsClass(const std::string& name);

    std::string headConstantName(ExpressionPointer typeExpression);

    // If `type` is `Ring.carrier(bundle)` / `CommutativeRing.carrier(bundle)`
    // and `bundle` WHNF-reduces to a `<Struct>.make(carrier, …)`
    // constructor, return the `carrier` field AS WRITTEN (not further
    // reduced) — otherwise nullptr. Lets operator dispatch resolve a value
    // typed by a carrier projection over a CONCRETE ring to the concrete
    // carrier head (`Polynomial(…)`), without over-reducing it to the
    // underlying `Quotient(…)` the way full WHNF would. An abstract
    // `Ring.carrier(s)` has a stuck bundle argument, so this returns
    // nullptr and the dispatch is unchanged.
    ExpressionPointer carrierProjectionField(ExpressionPointer type);

    // Walk `signature`'s Pi chain; check that the first N domains have
    // the head-name listed in `argumentTypeNames`. Requires the chain
    // to have AT LEAST N Pis — partial application of an overloaded
    // name is not allowed (we want exact-arity calls).
    bool signatureAcceptsArgumentTypes(
        ExpressionPointer signature,
        const std::vector<std::string>& argumentTypeNames);

    // Helper: decompose `expectedType` (or any type expression) as
    // `Quotient(T, R)` and return T, R, and the universe level u such
    // that T : Type(u). Returns nullopt if the expression isn't a
    // Quotient application.
    struct QuotientDecomposition {
        ExpressionPointer carrierType;
        ExpressionPointer relation;
        LevelPointer universeLevel;
    };
    bool tryDecomposeQuotient(
        ExpressionPointer typeExpression,
        QuotientDecomposition& result);

    // `Quotient.mk(rep)` — desugars to `Quotient.mk.{u}(T, R, rep)`,
    // recovering `T` from `rep`'s inferred type and `R` (plus
    // confirming `T`) from the expected type when available.
    ExpressionPointer desugarQuotientMk(
        SurfaceExpressionPointer representativeSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // `Quotient.sound(x, y, proof)` — desugars to
    // `Quotient.sound.{u}(T, R, x, y, proof)`. Recovers `T` from `x`'s
    // type and `R` by walking `proof`'s type as `R(x, y)` to extract
    // the head `R`.
    ExpressionPointer desugarQuotientSound(
        SurfaceExpressionPointer xSurface,
        SurfaceExpressionPointer ySurface,
        SurfaceExpressionPointer proofSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // `And.eliminate(handler, conjunction)` — short form. Desugars to
    // the verbose `And.eliminate(A, B, Goal, handler, conjunction)`.
    ExpressionPointer desugarAndEliminate(
        SurfaceExpressionPointer handlerSurface,
        SurfaceExpressionPointer conjSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // `Or.eliminate(handleLeft, handleRight, disjunction)` — short
    // form. Desugars to `Or.eliminate(A, B, Goal, handleLeft,
    // handleRight, disjunction)`.
    ExpressionPointer desugarOrEliminate(
        SurfaceExpressionPointer handleLeftSurface,
        SurfaceExpressionPointer handleRightSurface,
        SurfaceExpressionPointer disjSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // `Exists.eliminate(handler, witness)` — short form. Desugars to
    // the verbose `Exists.eliminate(A, P, Goal, handler, witness)` by
    // recovering A and P from `witness`'s type (`Exists(A, P)`) and
    // Goal from the call-site expectedType.
    //
    // The handler must have type `(w : A) → P(w) → Goal`. We build
    // that Pi-chain as the expected type for the handler so the
    // user-side lambda can be type-driven (no need to annotate the
    // binders).
    //
    // Subtle: the contract of `expectedType` here is *closed* form
    // — BoundVariable indices already account for the call-site's
    // enclosing Pi/Lambda binders. `aType` / `predicate` extracted
    // from the witness's *inferred* type are in *opened* form
    // (Internal FreeVariables, since `inferTypeInLocalContext`
    // opens). Mixing the two without conversion produces dangling
    // BoundVariables or unbound FreeVariables in the assembled
    // call. See the close/no-close discipline at the end.
    ExpressionPointer desugarExistsEliminate(
        SurfaceExpressionPointer handlerSurface,
        SurfaceExpressionPointer witnessSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // `Quotient.lift(f, h, q)` — desugars to
    // `Quotient.lift.{u, v}(T, R, U, f, h, q)`. Recovers everything
    // from the argument types: `T → U` is `f`'s Pi signature; `R`
    // appears in `q`'s type as `Quotient(T, R)`.
    ExpressionPointer desugarQuotientLift(
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer hSurface,
        SurfaceExpressionPointer qSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // True when `surface` is the bare `_` placeholder identifier.
    bool isUnderscorePlaceholder(SurfaceExpressionPointer surface) const;

    // Synthesize a `Quotient.induct` motive by abstracting `qKernel` in
    // `expectedType`. Returns `Lambda(q' : Quotient(T, R), goal[q ↦ q'])`
    // in closed form. Caller is responsible for providing a non-null
    // `expectedType`.
    ExpressionPointer inferQuotientMotive(
        ExpressionPointer expectedType,
        ExpressionPointer qKernel,
        ExpressionPointer qTypeOpenedAsDomain,
        const std::vector<LocalBinder>& localBinders);

    // `Quotient.induct(motive, f, q)` — desugars to
    // `Quotient.induct.{u}(T, R, motive, f, q)`. Recovers T, R from
    // `q`'s type `Quotient(T, R)`. `motiveSurface` may be `nullptr` (the
    // 2-arg form `Quotient.induct(f, q)`) or the bare `_` identifier,
    // in which case the motive is inferred from the expected type by
    // abstracting `q`.
    ExpressionPointer desugarQuotientInduct(
        SurfaceExpressionPointer motiveSurface,
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer qSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // Synthesize a `Quotient.induct_two` motive by sequentially
    // abstracting q2 (innermost) and q1 (outermost). Returns
    // `Lambda(q1' : Q1, Lambda(q2' : Q2, goal[q1 ↦ q1', q2 ↦ q2']))` in
    // closed form. After the two abstract calls, q1 occurrences in the
    // expectedType are at BV(1) and q2 occurrences are at BV(0); local
    // binders are shifted by +2.
    ExpressionPointer inferQuotientMotiveTwo(
        ExpressionPointer expectedType,
        ExpressionPointer q1Kernel,
        ExpressionPointer q2Kernel,
        ExpressionPointer q1TypeOpenedAsDomain,
        ExpressionPointer q2TypeOpenedAsDomain,
        const std::vector<LocalBinder>& localBinders);

    // `Quotient.induct_two(motive, f, q1, q2)` — recovers T1, R1, T2,
    // R2 from `q1` and `q2`'s types (each of the form `Quotient(Ti, Ri)`)
    // and emits `Quotient.induct_two.{u, v}(T1, R1, T2, R2, motive, f,
    // q1, q2)`. `motiveSurface` may be `nullptr` (the 3-arg form
    // `Quotient.induct_two(f, q1, q2)`) or the bare `_` identifier,
    // in which case the motive is inferred from the expected type.
    ExpressionPointer desugarQuotientInductTwo(
        SurfaceExpressionPointer motiveSurface,
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer q1Surface,
        SurfaceExpressionPointer q2Surface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // `Quotient.induct_three(motive, f, q1, q2, q3)` — recovers T1, R1,
    // T2, R2, T3, R3 from `q1`, `q2`, `q3`'s types and emits
    // `Quotient.induct_three.{u, v, w}(T1, R1, T2, R2, T3, R3, motive,
    //                                    f, q1, q2, q3)`.
    // Synthesize a `Quotient.induct_three` motive by abstracting q3,
    // q2, q1 from innermost to outermost. Returns
    // `Lambda(q1', Lambda(q2', Lambda(q3', goal[...])))` in closed form,
    // where q3 → BV(0), q2 → BV(1), q1 → BV(2) and local binders are
    // shifted by +3.
    ExpressionPointer inferQuotientMotiveThree(
        ExpressionPointer expectedType,
        ExpressionPointer q1Kernel,
        ExpressionPointer q2Kernel,
        ExpressionPointer q3Kernel,
        ExpressionPointer q1TypeOpenedAsDomain,
        ExpressionPointer q2TypeOpenedAsDomain,
        ExpressionPointer q3TypeOpenedAsDomain,
        const std::vector<LocalBinder>& localBinders);

    ExpressionPointer desugarQuotientInductThree(
        SurfaceExpressionPointer motiveSurface,
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer q1Surface,
        SurfaceExpressionPointer q2Surface,
        SurfaceExpressionPointer q3Surface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/);

    // Given a `Sort u`-shape level, return the predecessor `u-1`. Used
    // by the quotient desugars to back out the universe parameter from
    // a type's type.
    LevelPointer predecessorOfSortLevel(LevelPointer sortLevel);

    ExpressionPointer desugarCongruenceOf(
        SurfaceExpressionPointer functionSurface,
        SurfaceExpressionPointer equalityProofSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int column);

    // Open the innermost `count` local binders of `term` into FreeVariables
    // (one per binder, by name, with Internal origin so they don't collide
    // with user names). Returns the opened term suitable for inferType when
    // paired with a matching Context built from the same binders.

    // Inverse of openOverLocalBinders: converts the Internal-origin
    // FreeVariables introduced by opening back into BoundVariables so the
    // term can be embedded in a context with the same binders. Closes
    // outermost-first (the reverse order of opening), so the resulting
    // BoundVariable indices line up.

    // Build the kernel Context corresponding to `localBinders`: for each
    // binder, open its type over earlier binders and (when the binder is
    // a let-binding with a value) its value too. Centralizes the
    // ~13 ad-hoc loops that previously built this by hand; their value
    // propagation is what enables isDefinitionallyEqual to ζ-reduce
    // FreeVariables back to let-bound values.

    // ζ-unfold every reference to a let-bound binder in `term` (a term
    // in closed-over-localBinders form), replacing it with the let's
    // value. Returns `term` unchanged when no let-binders are in scope.
    //
    // The auto-prover's structural matchers (tryLemmaIndexLookup,
    // tryClassifyDiff) walk terms by syntactic shape rather than
    // calling isDefinitionallyEqual on sub-positions, so they don't
    // benefit from the kernel-level δ-reduction on let-bound
    // FreeVariables. Calling this helper on cursors before matching
    // exposes the underlying expressions so library lemmas about V
    // match goals stated in terms of X (the let-name).

    // Walks `expression` and replaces every FreeVariable whose name is a
    // key in `assignment` with the corresponding replacement, lifting the
    // replacement by the number of binders we've descended into. Used to
    // substitute inferred constructor-parameter values back into Pi
    // domains and result types during parameter inference.

    // Returns true if `expression` contains an Internal-origin
    // FreeVariable whose name starts with `_constructorValueArgument_`
    // or `_callTrailingArgument_` — both are trailing-arg placeholders
    // opened during the backward-inference result-type probe. Targets
    // that mention any such placeholder aren't substituted away later
    // and would leak into the assembled kernel term, so the unifier
    // rejects them.
    // True if `expression` contains a FreeVariable whose name is in
    // `names` (used to detect unresolved leading-inference metavariables).
    bool containsNamedFreeVariable(
        ExpressionPointer expression,
        const std::set<std::string>& names);

    bool containsValueArgumentFreeVar(ExpressionPointer expression);

    // Walks `pattern` and `target` in parallel. Whenever pattern is a
    // FreeVariable whose name is in `metavariableNames` (and isn't yet
    // assigned), records `assignment[name] = target`. For Pi/Lambda/
    // Application, recurses into matching positions. For mismatches
    // (different shapes, different Constants, etc.), simply stops at
    // that subterm — we don't error out, since the caller may still
    // be able to fill the metavariable from other unification sources.
    //
    // Limitation: we only record assignments when binderDepth == 0,
    // because the captured `target` would otherwise live in a binder
    // context that doesn't match where the assignment is later used.
    // For the common cases (parameters appearing at the top level of
    // value-arg domains or as direct args of the result type's
    // applications), this is sufficient.
    // Walks a term and returns true if it references any BoundVariable
    // whose index is < threshold (i.e. it captures a binder we
    // descended into). Used to gate metavariable assignment under
    // binders: we can lift target up to the outer scope only when no
    // such "captured" references are present.

    // One δ-step on a (possibly applied) Constant-headed expression:
    // unfold the head definition and β-reduce the spine arguments into
    // it, WITHOUT recursing further — the result's head may itself be a
    // definition (e.g. `FiniteField(p,f)` → `RingModulo(…)`, whose head
    // `RingModulo` is in turn a definition for `Quotient(…)`). Stopping
    // after a single unfold is exactly what lets a head-directed matcher
    // stop at the FIRST head that aligns with its pattern, rather than
    // collapsing all the way to `Quotient`. Returns null when the head
    // isn't a transparent definition (axiom / opaque / inductive / not a
    // Constant), i.e. when no δ-step is available.
    ExpressionPointer unfoldHeadConstantOneStep(ExpressionPointer expr);

    void unifyConstructorParameters(
        ExpressionPointer pattern,
        ExpressionPointer target,
        const std::set<std::string>& metavariableNames,
        std::map<std::string, ExpressionPointer>& assignment,
        int binderDepth = 0,
        std::vector<ExpressionPointer>* binderTypeStack = nullptr);

    // Heads match when both are the same Constant (same name + universe
    // arguments), the same BoundVariable index, or the same Sort. A
    // FreeVariable head means a metavariable case — handled separately.
    bool headsMatch(ExpressionPointer left, ExpressionPointer right);

    // Calls the kernel's inferType on `term` interpreted under the given
    // local binder stack. Builds a kernel Context with FreeVariables for
    // each binder and opens the term to refer to them.
    ExpressionPointer inferTypeInLocalContext(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term);

    // For a term whose type is in some universe — i.e. the type's type is
    // a Sort N — returns the level u such that the term has type Type(u)
    // (i.e. u = N - 1). Throws if the predecessor cannot be computed
    // syntactically (e.g. a polymorphic Sort whose level is not a
    // LevelSuccessor or a concrete LevelConst).
    LevelPointer typeUniverseOf(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term);

    static const std::vector<std::string>& declarationUniverseParameters(
        const Declaration& declaration);

    static ExpressionPointer declarationType(
        const Declaration& declaration);

    // Unifies a single level expression with a concrete level, collecting
    // assignments for universe-parameter names. The "expected" side comes
    // from the signature being instantiated (may contain LevelParams that
    // are unsolved); the "actual" side is the level inferred from the
    // user's argument. Only handles cases we encounter in practice
    // (LevelParam, LevelSuccessor, LevelConst, LevelMax of constant-or-
    // parameter).
    void unifyLevels(
        LevelPointer expected, LevelPointer actual,
        std::map<std::string, LevelPointer>& assignment);

    void unifyTypes(
        ExpressionPointer expected, ExpressionPointer actual,
        std::map<std::string, LevelPointer>& assignment);

    // Stage 2 universe inference: when the user writes `Equality(A, x, y)`
    // without `.{u}`, look at the declaration's universe parameters and
    // value-argument types to derive the universe instantiation. Returns
    // the inferred universe arguments in declaration order. Universe
    // parameters that cannot be derived are defaulted to LevelConst(0).
    //
    // `skipLeadingPis` skips that many Pi binders before aligning the
    // value arguments with the remaining Pis. This lets the same routine
    // serve declarations with an implicit-arg prefix the user did NOT
    // pass — the caller infers those implicits separately.
    std::vector<LevelPointer> inferUniverseArguments(
        const Declaration& declaration,
        const std::vector<ExpressionPointer>& valueArguments,
        const std::vector<LocalBinder>& localBinders,
        int skipLeadingPis = 0,
        const std::string& callSiteName = "",
        bool errorOnUninferred = false);

    static size_t universeParameterCount(const Declaration& declaration);

    // ---- universe metavariable state ----
    // Each call to a declaration handler resets these. As elaboration
    // proceeds, each bare `Type` in the source generates a fresh
    // universe parameter name; the name is appended both to the
    // ordered/set views of "available universe parameters" (so internal
    // self-references can use it) and to autoBoundUniverseParameters_,
    // which is folded into the kernel declaration's universe parameter
    // list at the end of the handler.
    // Defined out-of-line in elaborator_levels.cpp.
    std::string freshAutoBoundUniverseName();
    void resetAutoBoundState();
    std::vector<std::string> finalUniverseParameters(
        const std::vector<std::string>& userDeclared);

    Environment& environment_;
    std::vector<std::string>& importedModules_;
    std::string moduleName_;
    // See elaborateModule's docstring. Consulted only by searchSuggestions
    // on a failed proof, to surface unimported library lemmas.
    std::function<const LibrarySearchIndex*()> librarySearchProvider_;
    // Tactic stats — tracks per-strategy invocations, successes, and
    // cumulative time. Enabled by MATH_TIME_TACTICS=1 env var. Dumped
    // by ~Elaborator if any tactic was instrumented.
    struct TacticStats {
        long long invocations = 0;
        long long successes = 0;
        long long totalMicros = 0;
    };
    std::unordered_map<std::string, TacticStats> tacticStats_;
    bool tacticTimingEnabled_ = false;

    // Auto-prover profiling — when MATH_PROFILE_AUTOPROVER=1, each
    // outermost call to autoProveClaim runs ALL tactics (not just
    // until the first success) and emits one row per claim site
    // describing which tactic won, where the winning fact came from
    // (local binder index, library name), how many candidates were
    // tried, and how long each tactic took. Recursive sub-calls
    // aggregate but do not emit rows.
    bool autoProveProfileEnabled_ = false;
    // Stage-1 statements-only mode (skip proof bodies). See constructor.
    bool statementsOnly_ = false;
    int autoProveDepth_ = 0;
    // Recursion guard for the symmetry-flip tactic: proving `x = y` by
    // proving `y = x` and wrapping in symmetry must not flip back to
    // `x = y`. Allowed only at depth 0.
    int symmetryFlipDepth_ = 0;
    // Set by tryContextFactMatch (only when profiling is on) to the
    // `source` string of whichever fact closed the goal. Read by
    // autoProveClaim's profiling path immediately after the tactic
    // returns, then cleared.
    std::string lastContextFactWinner_;
    int lastContextFactCandidateCount_ = 0;
    struct AutoProveAttempt {
        std::string tacticName;
        bool succeeded;
        long long micros;
        // Tactic-specific winner descriptor — for contextFactMatch
        // this is the ContextFact's `source` string (e.g.
        // "local binder kEqualsPredecessor", "library Natural.le_through_max_left").
        // Empty for tactics that don't have a meaningful winner.
        std::string winner;
        // For contextFactMatch: number of candidates the matcher
        // tried before finding (or failing to find) a winner.
        int candidatesTried = 0;
    };
    struct AutoProveRow {
        std::string moduleName;
        int line;
        std::string goalHead;
        size_t goalSize;
        std::string winningTactic;  // first tactic to succeed, or empty
        std::vector<AutoProveAttempt> attempts;
    };
    std::vector<AutoProveRow> autoProveRows_;

    // Per-decide-invocation memoization for the motive walker
    // (abstractStructuralOccurrenceWithWHNF). The walker visits the
    // same subterms repeatedly when WHNF unfolds expose recurring
    // structure. Caching by raw expression pointer at depth 0 (the
    // dominant case — depth > 0 only occurs inside Pi/Lambda/Let
    // binders, which are rare in the user-value path) collapses the
    // duplicated work. Cleared at the start of each elaborateDecide.
    struct MotiveWalkerCacheEntry {
        ExpressionPointer result;
        int occurrenceDelta;
        int whnfFuelDelta;  // amount of fuel CONSUMED by this call
    };
    std::unordered_map<Expression*, MotiveWalkerCacheEntry>
        motiveWalkerCache_;
    bool reportRedundantBy_ = false;
    bool reportRedundantByNonEq_ = false;
    bool reportRedundantCalcSteps_ = false;
    // Records, for the most recent `inferCallWithHoles` call, every PROOF
    // hole that was discharged from an in-scope hypothesis rather than the
    // goal: (depth = de Bruijn distance from innermost binder, 0 = the
    // immediately preceding binder; total = local binder count; name = the
    // matched binder's name). Read by the args-inferable diagnostic to emit
    // BY_DISCHARGE_STATS lines characterising where the discharged proof
    // lives. Cleared at the top of every `inferCallWithHoles`.
    std::vector<std::tuple<int, int, std::string>> lastDischarges_;
    std::string currentDeclarationName_;
    // `ring` over a bundled-ring carrier `Ring.carrier(s)`: the leading
    // structure argument(s) (`[s]`) that every operation/law term carries
    // before its operands in the kernel — e.g. `Ring.add(s, x, y)`,
    // `Ring.add_associative(s, …)`. Empty for a concrete carrier (whose
    // operations like `Integer.add(x, y)` take no leading structure arg).
    // Set via `RingStructurePrefixGuard` for the duration of one `ring`
    // elaboration; consumed by `ringConst` (term/law head builder) and by
    // the operation matchers.
    std::vector<ExpressionPointer> ringStructurePrefix_;
    // Stack of expected types active on the current elaboration call
    // chain. The top of the stack is what the `goal` keyword resolves
    // to. Pushed at the entry to elaborateExpression whenever the
    // call carries a non-null expectedType; popped on return via the
    // GoalScope RAII guard.
    std::vector<ExpressionPointer> goalStack_;
    // `unfold X in <body>` flips X's opacity from Opaque to
    // Transparent and records the original opacity here. The list is
    // drained at the end of each top-level definition / theorem so
    // the kernel's final typecheck (inside addDefinition) also sees
    // the unfolded view. One theorem's `unfold` doesn't leak to the
    // next.
    std::vector<std::pair<std::string, Opacity>>
        pendingOpacityRestores_;
    // Conventions registered via `convention p [q ...] : T [with …];`
    // declarations. Keyed by name. When a subsequent declaration's
    // signature or body mentions a key as a free identifier, the
    // elaborator auto-prepends `{p : T}` and one implicit binder per
    // side-condition. v1: file-local (cleared at module start would be
    // ideal but for now lives for the entire elaborator instance, which
    // matches the per-module verifier invocation).
    struct ConventionEntry {
        SurfaceExpressionPointer type;
        std::vector<SurfaceConventionProposition> propositions;
    };
    std::unordered_map<std::string, ConventionEntry> conventionRegistry_;
    // Names declared via `construction` — canonical quotient-introduction
    // forms. They are ordinary transparent definitions; this set records
    // which definitions are the preferred named introduction so that
    // `by_representatives` (and, later, the printer) can fold a
    // representative term back to the named form.
    std::set<std::string> canonicalConstructions_;
    // The canonical-instance registry itself lives on `environment_`
    // (kernel.hpp `Environment::canonicalInstanceRegistry`) so it persists
    // across module imports, like the coercion/operator/overload
    // registries. See elaborateInstanceDeclaration (registration, with
    // reject-on-ambiguity) and the resolution pass in inferLeadingArguments.
    // Memoized result of "does definition X's body transitively
    // reference constant Y as a head?" — used by the `decide`
    // elaborator's WHNF walker to skip Applications whose head
    // can't δ-unfold to expose the target. Keyed by
    // "<X>|<Y>" (a flat string so std::unordered_map works).
    mutable std::unordered_map<std::string, bool>
        unfoldExposesHeadCache_;
    // Phase 3 lemma index. Each registered rewrite lemma — anything of
    // shape `Π x₁ … xₙ. Equality.{u}(carrier, LHS, RHS)` with no
    // universe parameters — is keyed by `spineHash(LHS)` (and again by
    // `spineHash(RHS)` so a reverse-direction lookup works without a
    // separate scan). At calc-step classify time we hash the diff,
    // pull candidates from the bucket, run a small first-order matcher,
    // substitute the matched bindings into the lemma's RHS, and verify
    // structural equality against the other endpoint. This subsumes
    // the bespoke commutativity/associativity/identity classifiers and
    // additionally fires on any user-written rewrite lemma whose LHS
    // matches the diff.
    struct RewriteLemma {
        std::string lemmaName;
        int binderCount = 0;
        // LHS / RHS in closed-over-binders form: BoundVariable(0..n-1)
        // refer to the lemma's binders, BV(0) being the *innermost*.
        ExpressionPointer lhs;
        ExpressionPointer rhs;
        // Each binder's type, lifted into the conclusion's frame so
        // `instantiateLemmaBinders` can substitute the metavariable
        // bindings directly. `binderTypes[i]` is the type of the
        // binder with conclusion-frame de Bruijn index i (0 =
        // innermost, n-1 = outermost). Used to discharge propositional
        // preconditions when pattern matching the LHS/RHS leaves some
        // binders unbound (e.g. `primality` / positivity proofs on
        // `padic_valuation_multiplicative`).
        std::vector<ExpressionPointer> binderTypes;
        // Set when this entry indexes the lemma's RHS (so a hash hit
        // means we matched the wrong side and must emit
        // `Equality.symmetry`).
        bool reverseDirection = false;
    };
    std::unordered_multimap<uint64_t, RewriteLemma> lemmaIndex_;
    // Context frames describing what the elaborator is currently doing.
    // Each frame is a short phrase like "while elaborating cases at
    // line 42". `Frame` is an RAII guard that pushes on construction
    // and pops on destruction; `throwElaborate` (and the kernel-error
    // catch path) prepends the frames to the diagnostic so the user
    // sees a breadcrumb trail from their source line to the failure.
    std::vector<FrameSnapshot> contextFrames_;
    // Ordered list of universe parameters of the current declaration —
    // ordered so we can auto-fill universe arguments at self-reference
    // sites (the user writes `Equality(A, x, x)` inside reflexivity's
    // constructor type; we elaborate it as `Equality.{u}(A, x, x)`).
    // Auto-bound names are appended as bare `Type` is encountered.
    std::vector<std::string> currentUniverseParametersOrdered_;
    std::set<std::string> currentUniverseParameters_;
    std::vector<std::string> autoBoundUniverseParameters_;
    int metavarCounter_ = 0;
};

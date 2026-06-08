// Out-of-line Elaborator method definitions: the run* drivers (runModule / runExpression / runTactic), profiling output, and configuration setters
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

void Elaborator::emitAutoProverProfile() {
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

void Elaborator::setReportRedundantBy(bool flag) { reportRedundantBy_ = flag; }

void Elaborator::setReportUnusedNames(bool flag) { reportUnusedNames_ = flag; }

void Elaborator::setLibrarySearchProvider(
        std::function<const LibrarySearchIndex*()> provider) {
        librarySearchProvider_ = std::move(provider);
    }

void Elaborator::setReportRedundantByNonEq(bool flag) {
        reportRedundantByNonEq_ = flag;
    }

void Elaborator::setReportRedundantCalcSteps(bool flag) {
        reportRedundantCalcSteps_ = flag;
    }

void Elaborator::runModule(const SurfaceModule& module) {
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

std::string Elaborator::topStatementLabel(
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

void Elaborator::seedAlgebraicRegistryFromEnvironment() {
        for (const auto& entry : environment_.declarations) {
            const std::string& name = entry.first;
            const auto& declaration = entry.second;
            if (auto* def = std::get_if<Definition>(&declaration)) {
                registerAlgebraicShape(name, def->type);
            }
        }
    }

ExpressionPointer Elaborator::runExpression(const SurfaceExpression& expression) {
        return elaborateExpression(expression, {});
    }


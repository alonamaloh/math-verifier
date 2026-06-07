// Out-of-line Elaborator method definitions: the auto-prover (context facts/equalities, transitivity/symmetry bridges, autoProveClaim)
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

#include <cstdlib>
#include <iostream>

namespace {
// Warn threshold for an expensive-but-successful by-less auto-prove, in
// kernel reduction steps. Overridable via MATH_AUTOPROVE_WARN (0
// disables). Default picked from the library's step distribution: well
// above p99 (~24k) so only genuine outliers fire, well below the hard
// budget so it surfaces first.
long long autoProveWarnThresholdValue() {
    static long long cached = [] {
        if (const char* w = std::getenv("MATH_AUTOPROVE_WARN")) {
            char* end = nullptr;
            long long v = std::strtoll(w, &end, 10);
            if (end != w && v >= 0) return v;
        }
        return 50000LL;
    }();
    return cached;
}
}  // namespace

long long Elaborator::autoProveWarnThreshold() {
    return autoProveWarnThresholdValue();
}

namespace {
// Effort cap (kernel reduction steps) for the speculative re-proof in the
// redundancy checks. Stricter than the warn threshold on purpose: a hint is
// only "redundant" if the by-less re-proof is near-free, so cleanup never
// trades a fast proof for a merely-under-the-warning one. Overridable via
// MATH_REDUNDANT_BUDGET (0 disables → use the default auto-prove budget).
long long redundancyBudgetValue() {
    static long long cached = [] {
        if (const char* w = std::getenv("MATH_REDUNDANT_BUDGET")) {
            char* end = nullptr;
            long long v = std::strtoll(w, &end, 10);
            if (end != w && v >= 0) return v;
        }
        return 10000LL;
    }();
    return cached;
}
}  // namespace

long long Elaborator::redundancyBudget() {
    return redundancyBudgetValue();
}

ExpressionPointer Elaborator::tryContradiction(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/) {
        if (!environment_.lookup(
                "False.eliminate_proposition")) {
            return nullptr;
        }
        int N = static_cast<int>(localBinders.size());
        if (N == 0) return nullptr;
        int lastIdx = N - 1;
        int lastLift = N - lastIdx;
        ExpressionPointer lastTypeOpened = openOverLocalBinders(
            liftBoundVariables(
                localBinders[lastIdx].type, lastLift, 0),
            localBinders, N);
        // Pass 1: most-recent binder is itself `False`.
        {
            auto* asConst = std::get_if<Constant>(
                &lastTypeOpened->node);
            if (asConst && asConst->name == "False") {
                ExpressionPointer call = makeConstant(
                    "False.eliminate_proposition", {});
                call = makeApplication(call, goalClosed);
                call = makeApplication(
                    call,
                    makeBoundVariable(N - 1 - lastIdx));
                return call;
            }
        }
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        // Pass 2: (last, other) pair where one is `Not(P)` and the
        // other is `P`. Try BOTH orderings: last is Not(P) paired
        // with some other = P; or last is P paired with some other
        // = Not(P).
        auto buildProofOfFalse =
            [&](ExpressionPointer notHyp,
                ExpressionPointer pHyp) -> ExpressionPointer {
                ExpressionPointer call = makeConstant(
                    "False.eliminate_proposition", {});
                call = makeApplication(call, goalClosed);
                call = makeApplication(
                    call, makeApplication(notHyp, pHyp));
                return call;
            };
        // Case A: last : Not(P). Find some other : P.
        if (auto* pi =
                std::get_if<Pi>(&lastTypeOpened->node)) {
            auto* codomainConst = std::get_if<Constant>(
                &pi->codomain->node);
            if (codomainConst
                && codomainConst->name == "False") {
                ExpressionPointer expectedP = pi->domain;
                for (int other = N - 2; other >= 0; --other) {
                    int lift = N - other;
                    ExpressionPointer otherType =
                        openOverLocalBinders(
                            liftBoundVariables(
                                localBinders[other].type,
                                lift, 0),
                            localBinders, N);
                    if (isDefinitionallyEqual(
                            environment_, openedContext,
                            otherType, expectedP)) {
                        return buildProofOfFalse(
                            makeBoundVariable(
                                N - 1 - lastIdx),
                            makeBoundVariable(
                                N - 1 - other));
                    }
                }
            }
        }
        // Case B: last : P. Find some other : Not(P).
        for (int other = N - 2; other >= 0; --other) {
            int lift = N - other;
            ExpressionPointer otherType = openOverLocalBinders(
                liftBoundVariables(
                    localBinders[other].type, lift, 0),
                localBinders, N);
            auto* pi = std::get_if<Pi>(&otherType->node);
            if (!pi) continue;
            auto* codomainConst = std::get_if<Constant>(
                &pi->codomain->node);
            if (!codomainConst
                || codomainConst->name != "False") continue;
            if (!isDefinitionallyEqual(
                    environment_, openedContext,
                    pi->domain, lastTypeOpened)) continue;
            return buildProofOfFalse(
                makeBoundVariable(N - 1 - other),
                makeBoundVariable(N - 1 - lastIdx));
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryDisjunctionIntro(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        auto* outerApp = std::get_if<Application>(&goalOpened->node);
        if (!outerApp) return nullptr;
        auto* innerApp = std::get_if<Application>(
            &outerApp->function->node);
        if (!innerApp) return nullptr;
        auto* head = std::get_if<Constant>(&innerApp->function->node);
        if (!head || head->name != "Or") return nullptr;
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer aClosed = closeOverLocalBinders(
            innerApp->argument, localBinders, N);
        ExpressionPointer bClosed = closeOverLocalBinders(
            outerApp->argument, localBinders, N);
        // Try Or.introduceLeft (prove A).
        if (environment_.lookup("Or.introduceLeft")) {
            ExpressionPointer proofA;
            try {
                proofA = autoProveClaim(
                    aClosed, localBinders, line);
            } catch (const ElaborateError&) { proofA = nullptr; }
              catch (const TypeError&) { proofA = nullptr; }
            if (proofA) {
                ExpressionPointer call = makeConstant(
                    "Or.introduceLeft", {});
                call = makeApplication(call, aClosed);
                call = makeApplication(call, bClosed);
                call = makeApplication(call, proofA);
                return call;
            }
        }
        // Fall through to Or.introduceRight (prove B).
        if (environment_.lookup("Or.introduceRight")) {
            ExpressionPointer proofB;
            try {
                proofB = autoProveClaim(
                    bClosed, localBinders, line);
            } catch (const ElaborateError&) { proofB = nullptr; }
              catch (const TypeError&) { proofB = nullptr; }
            if (proofB) {
                ExpressionPointer call = makeConstant(
                    "Or.introduceRight", {});
                call = makeApplication(call, aClosed);
                call = makeApplication(call, bClosed);
                call = makeApplication(call, proofB);
                return call;
            }
        }
        return nullptr;
    }

std::vector<Elaborator::ContextFact> Elaborator::collectContextFacts(
        ExpressionPointer /*goalClosed*/,
        const std::vector<LocalBinder>& localBinders,
        uint64_t goalHash,
        uint64_t goalHashUnreduced) {
        std::vector<ContextFact> facts;
        int N = static_cast<int>(localBinders.size());
        // Local binders (cost 1) — last-bound first, so the most
        // recent fact wins on ties when the matcher returns.
        for (int b = N - 1; b >= 0; --b) {
            int lift = N - b;
            ContextFact fact;
            fact.cost = 1;
            fact.source = "local binder " + localBinders[b].name;
            fact.proofTerm = makeBoundVariable(N - 1 - b);
            fact.type = liftBoundVariables(
                localBinders[b].type, lift, 0);
            facts.push_back(std::move(fact));
        }
        // Library / module declarations (cost 3) — only those whose
        // conclusion's spine matches the goal's at SOME peel depth.
        // Match against BOTH the goal's WHNF-reduced spineHash AND
        // its un-reduced one: a lemma whose stated conclusion uses a
        // definitional alias (e.g. `Rational.LessOrEqual.reflexive :
        // x ≤ x` where `≤` unfolds to `IsNonneg(_ - _)`) is indexed
        // by the alias `LessOrEqual`, but the goal is WHNF'd to
        // `IsNonneg`, so a single-hash match misses it. Comparing
        // both un-reduced and reduced catches the lemma in either
        // direction.
        // Universe-polymorphic candidates are skipped (universe-arg
        // inference at use-site isn't wired up).
        for (const auto& entry : environment_.declarations) {
            const std::string& name = entry.first;
            const auto& declaration = entry.second;
            ExpressionPointer declarationType;
            size_t universeParamCount = 0;
            if (auto* def =
                    std::get_if<Definition>(&declaration)) {
                declarationType = def->type;
                universeParamCount =
                    def->universeParameters.size();
            } else if (auto* ax =
                           std::get_if<Axiom>(&declaration)) {
                declarationType = ax->type;
                universeParamCount =
                    ax->universeParameters.size();
            } else if (auto* ctor =
                           std::get_if<Constructor>(&declaration)) {
                declarationType = ctor->type;
                universeParamCount =
                    ctor->universeParameters.size();
            } else {
                continue;
            }
            if (universeParamCount != 0) continue;
            bool anyDepthMatches = false;
            ExpressionPointer depthCursor = declarationType;
            while (true) {
                uint64_t hashAtDepth = spineHash(depthCursor);
                if (hashAtDepth == goalHash
                    || hashAtDepth == goalHashUnreduced) {
                    anyDepthMatches = true;
                    break;
                }
                auto* pi = std::get_if<Pi>(&depthCursor->node);
                if (!pi) break;
                depthCursor = pi->codomain;
            }
            if (!anyDepthMatches) continue;
            ContextFact fact;
            fact.cost = 3;
            fact.source = "library " + name;
            fact.proofTerm = makeConstant(name, {});
            fact.type = declarationType;
            facts.push_back(std::move(fact));
        }
        return facts;
    }

ExpressionPointer Elaborator::tryLemmaByConclusion(
        const std::string& name,
        ExpressionPointer lemmaType,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        int totalPi = countLeadingPis(lemmaType);
        if (totalPi == 0) return nullptr;
        std::vector<SurfaceExpressionPointer> holeArgs;
        for (int i = 0; i < totalPi; ++i) {
            holeArgs.push_back(makeSurfaceHole(line, 0));
        }
        std::vector<ExpressionPointer> resolved;
        try {
            resolved = inferCallWithHoles(
                name, lemmaType, holeArgs, localBinders, goalClosed, line);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
        ExpressionPointer call = makeConstant(name, {});
        for (auto& argument : resolved) {
            call = makeApplication(std::move(call), std::move(argument));
        }
        if (containsFreeVariable(call)) return nullptr;
        // Confirm it really proves the goal before handing it back.
        try {
            ExpressionPointer inferredOpened =
                inferTypeInLocalContext(localBinders, call);
            ExpressionPointer goalOpened = openOverLocalBinders(
                goalClosed, localBinders, localBinders.size());
            Context context = buildContextFromLocalBinders(localBinders);
            if (!isDefinitionallyEqual(environment_, context,
                                        inferredOpened, goalOpened)) {
                return nullptr;
            }
        } catch (...) {
            return nullptr;
        }
        return call;
    }

ExpressionPointer Elaborator::tryResolvePremiseSlot(
        ExpressionPointer slotTypeClosed,
        const std::vector<LocalBinder>& localBinders,
        std::set<std::string>& metavariableNames,
        std::map<std::string, ExpressionPointer>& assignment,
        int depth, int line) {
        autoProveSpend(1);
        if (depth >= kBackwardChainDepthCap) return nullptr;
        // Candidate lemmas by conclusion head. The slot may still contain
        // parent metavar free variables; computeGoalHits's head filter +
        // first-order match treat them as opaque, which is what we want (a
        // metavar in an ARGUMENT position doesn't change the conclusion head).
        ExpressionPointer slotOpened;
        try {
            slotOpened = openOverLocalBinders(
                slotTypeClosed, localBinders, localBinders.size());
        } catch (...) { return nullptr; }
        std::string head;
        std::vector<LemmaSearchHit> hits;
        try {
            static const std::set<std::string> noExclusions;
            hits = computeGoalHits(environment_, slotOpened, head, noExclusions);
        } catch (...) { return nullptr; }
        int tried = 0;
        for (const auto& hit : hits) {
            if (tried >= kBackwardChainCandidateCap) break;
            // In-scope lemmas only (computeGoalHits over environment_ already
            // ensures this, but be explicit).
            if (!environment_.lookup(hit.name)) continue;
            ++tried;
            ExpressionPointer proof = trySubLemmaSharingMetavars(
                hit.name, hit.declaredType, slotTypeClosed, localBinders,
                metavariableNames, assignment, line);
            if (proof) return proof;
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryGuessUndeterminedPremise(
        ExpressionPointer slotTypeClosed,
        const std::map<std::string, ExpressionPointer>& metavarTypes,
        const std::vector<LocalBinder>& localBinders,
        const std::set<std::string>& metavariableNames,
        std::map<std::string, ExpressionPointer>& assignment,
        int line) {
        autoProveSpend(1);
        // The slot must carry exactly one unresolved metavar: a single data
        // hole to guess. (Zero is 5d's job; two or more would explode.)
        std::vector<std::string> present;
        for (const auto& name : metavariableNames) {
            if (containsNamedFreeVariable(slotTypeClosed, {name})) {
                present.push_back(name);
            }
        }
        if (present.size() != 1) return nullptr;
        const std::string& metavar = present[0];
        auto typeIt = metavarTypes.find(metavar);
        if (typeIt == metavarTypes.end()) return nullptr;
        ExpressionPointer metavarType =
            substituteFreeVariables(typeIt->second, assignment);
        if (containsFreeVariable(metavarType)) return nullptr;
        Context context = buildContextFromLocalBinders(localBinders);
        ExpressionPointer metavarTypeOpened, slotOpened;
        try {
            metavarTypeOpened = openOverLocalBinders(
                metavarType, localBinders, localBinders.size());
            slotOpened = openOverLocalBinders(
                slotTypeClosed, localBinders, localBinders.size());
        } catch (...) { return nullptr; }
        int tried = 0;
        for (size_t bi = 0; bi < localBinders.size(); ++bi) {
            if (tried >= kBackwardChainCandidateCap) break;
            // The candidate binder must have the metavar's type.
            bool typeMatches = false;
            try {
                typeMatches = isDefinitionallyEqual(
                    environment_, context, localBinders[bi].type,
                    metavarTypeOpened);
            } catch (...) { typeMatches = false; }
            if (!typeMatches) continue;
            ++tried;
            ExpressionPointer candidate =
                openedLocalBinderReference(localBinders, bi);
            ExpressionPointer goalOpened = substituteFreeVariables(
                slotOpened, {{metavar, candidate}});
            ExpressionPointer goalClosed;
            try {
                goalClosed = closeOverLocalBinders(
                    goalOpened, localBinders, localBinders.size());
            } catch (...) { continue; }
            if (containsFreeVariable(goalClosed)) continue;
            ExpressionPointer proof = nullptr;
            try {
                proof = autoProveClaim(goalClosed, localBinders, line);
            } catch (const AutoProverBudgetError&) {
                return nullptr;
            } catch (...) { proof = nullptr; }
            if (proof) {
                assignment[metavar] = closeOverLocalBinders(
                    candidate, localBinders, localBinders.size());
                return proof;
            }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::trySubLemmaSharingMetavars(
        const std::string& name,
        ExpressionPointer lemmaType,
        ExpressionPointer slotTypeClosed,
        const std::vector<LocalBinder>& localBinders,
        std::set<std::string>& metavariableNames,
        std::map<std::string, ExpressionPointer>& assignment,
        int line) {
        autoProveSpend(1);
        int totalPi = countLeadingPis(lemmaType);
        if (totalPi == 0) return nullptr;
        std::vector<SurfaceExpressionPointer> holeArgs;
        for (int i = 0; i < totalPi; ++i) {
            holeArgs.push_back(makeSurfaceHole(line, 0));
        }
        // Apply the candidate as a sub-citation that SHARES the parent's
        // metavar set (so a leaf premise unification can solve a parent hole)
        // and reports which parent holes it solved. The sub-call's own Step 5e
        // is bounded by backwardChainingDepth_ (incremented here).
        std::map<std::string, ExpressionPointer> solvedInherited;
        std::vector<ExpressionPointer> resolved;
        ++backwardChainingDepth_;
        // Depth-tag the sub-call's diagnostic name so its fresh hole names
        // (`_hole_i_<diag>`) never collide with the parent's — crucial when a
        // lemma is applied to its own premise (self-application).
        std::string subDiag =
            name + "@bc" + std::to_string(backwardChainingDepth_);
        try {
            resolved = inferCallWithHoles(
                subDiag, lemmaType, holeArgs, localBinders, slotTypeClosed,
                line, &metavariableNames, &solvedInherited);
        } catch (...) {
            --backwardChainingDepth_;
            return nullptr;
        }
        --backwardChainingDepth_;
        // Compose the parent assignment with the holes this sub-call solved,
        // then substitute it (to a fixpoint) so the proof term and slot type
        // carry no leftover metavar free variables.
        std::map<std::string, ExpressionPointer> merged = assignment;
        for (const auto& kv : solvedInherited) {
            if (!merged.count(kv.first)) merged[kv.first] = kv.second;
        }
        auto resolveFully = [&](ExpressionPointer e) {
            for (int k = 0; k <= kBackwardChainDepthCap + 1
                            && containsFreeVariable(e); ++k) {
                e = substituteFreeVariables(e, merged);
            }
            return e;
        };
        ExpressionPointer call = makeConstant(name, {});
        for (auto& argument : resolved) {
            call = makeApplication(std::move(call), resolveFully(argument));
        }
        if (containsFreeVariable(call)) return nullptr;
        // The slot, with parent holes now substituted, must be hole-free and
        // the built proof must actually have that type (soundness backstop;
        // the kernel re-checks the whole citation afterwards regardless).
        ExpressionPointer slotResolved = resolveFully(slotTypeClosed);
        if (containsFreeVariable(slotResolved)) return nullptr;
        try {
            ExpressionPointer inferredOpened =
                inferTypeInLocalContext(localBinders, call);
            ExpressionPointer slotOpened = openOverLocalBinders(
                slotResolved, localBinders, localBinders.size());
            Context context = buildContextFromLocalBinders(localBinders);
            if (!isDefinitionallyEqual(environment_, context,
                                        inferredOpened, slotOpened)) {
                return nullptr;
            }
        } catch (...) {
            return nullptr;
        }
        // Commit the parent-hole solutions (only now, on full success).
        for (const auto& kv : solvedInherited) {
            if (!assignment.count(kv.first)) assignment[kv.first] = kv.second;
        }
        return call;
    }

ExpressionPointer Elaborator::tryContextFactMatch(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer goalReduced = weakHeadNormalForm(
            environment_, goalClosed);
        uint64_t goalHash = spineHash(goalReduced);
        uint64_t goalHashUnreduced = spineHash(goalClosed);
        std::vector<ContextFact> facts = collectContextFacts(
            goalClosed, localBinders, goalHash, goalHashUnreduced);
        std::sort(facts.begin(), facts.end(),
            [](const ContextFact& a, const ContextFact& b) {
                return a.cost < b.cost;
            });
        // Reset profiling fields each call — only meaningful when
        // autoProveProfileEnabled_, but the writes are cheap.
        lastContextFactWinner_.clear();
        lastContextFactCandidateCount_ = 0;
        int triedCount = 0;
        for (const ContextFact& fact : facts) {
            // Each candidate runs a structural fill (and possibly a full
            // hole-inference) — both trigger kernel conversions that can
            // be costly on goals mentioning expensive recursions. Charge
            // the budget and stop scanning if it's exhausted.
            autoProveSpend(1);
            ++triedCount;
            ExpressionPointer result;
            try {
                result = autoFillHintForClaim(
                    fact.proofTerm, fact.type, goalClosed,
                    localBinders, line);
            } catch (const ElaborateError&) {
                result = nullptr;
            } catch (const TypeError&) {
                result = nullptr;
            }
            // When the cheap structural fill fails, retry a library-lemma
            // candidate with the full hole-inference + context-discharge
            // machinery (see `tryLemmaByConclusion`). Only pays this cost
            // on candidates the structural path already rejected.
            if (!result) {
                if (auto* constantHead =
                        std::get_if<Constant>(&fact.proofTerm->node)) {
                    result = tryLemmaByConclusion(
                        constantHead->name, fact.type, goalClosed,
                        localBinders, line);
                }
            }
            if (result) {
                if (autoProveProfileEnabled_) {
                    lastContextFactWinner_ = fact.source;
                    lastContextFactCandidateCount_ = triedCount;
                }
                return result;
            }
        }
        if (autoProveProfileEnabled_) {
            lastContextFactCandidateCount_ = triedCount;
        }
        return nullptr;
    }

void Elaborator::collectLibraryEqualitiesAt(
        ExpressionPointer subexpr,
        const std::vector<LocalBinder>& localBinders,
        std::vector<ContextEquality>& out) {
        auto* app =
            std::get_if<Application>(&subexpr->node);
        if (!app) return;
        uint64_t key = spineHash(subexpr);
        auto range = lemmaIndex_.equal_range(key);
        for (auto iterator = range.first;
             iterator != range.second; ++iterator) {
            const RewriteLemma& lemma = iterator->second;
            ExpressionPointer pattern = lemma.reverseDirection
                ? lemma.rhs : lemma.lhs;
            if (std::holds_alternative<BoundVariable>(
                    pattern->node)) continue;
            std::vector<ExpressionPointer> bindings(
                lemma.binderCount);
            if (!matchAgainstPattern(
                    pattern, subexpr,
                    lemma.binderCount, bindings)) continue;
            bool allBound = true;
            for (auto& bn : bindings) {
                if (!bn) { allBound = false; break; }
            }
            if (!allBound) continue;
            ExpressionPointer lemmaApp = makeConstant(
                lemma.lemmaName, {});
            for (int i = lemma.binderCount - 1; i >= 0; --i) {
                lemmaApp = makeApplication(
                    lemmaApp, bindings[i]);
            }
            // Inferring the matched lemma's instantiated type runs a
            // conversion that, on a goal mentioning an expensive
            // recursion, can be the dominant per-candidate cost. Charge
            // the budget (throws AutoProverBudgetError once exhausted).
            autoProveSpend(2);
            ExpressionPointer lemmaAppType;
            try {
                lemmaAppType = inferTypeInLocalContext(
                    localBinders, lemmaApp);
            } catch (const TypeError&) { continue; }
              catch (const ElaborateError&) { continue; }
            EqualityComponents components;
            try {
                components = extractEqualityComponents(
                    lemmaAppType, "library lemma", 0);
            } catch (const ElaborateError&) { continue; }
            // inferTypeInLocalContext returns the type in OPENED
            // form (FVars for the local binders); close it so the
            // components live in the same closed scope as goalClosed,
            // which is what abstractStructuralOccurrence + substitute
            // expect.
            int N = static_cast<int>(localBinders.size());
            ContextEquality eq;
            eq.cost = 3;
            eq.source = "library lemma " + lemma.lemmaName;
            eq.carrierType = closeOverLocalBinders(
                components.carrierType, localBinders, N);
            eq.lhs = closeOverLocalBinders(
                components.leftEndpoint, localBinders, N);
            eq.rhs = closeOverLocalBinders(
                components.rightEndpoint, localBinders, N);
            eq.carrierLevel = components.carrierUniverseLevel;
            eq.proofExpr = lemmaApp;
            out.push_back(std::move(eq));
        }
        // Recurse into Application children.
        collectLibraryEqualitiesAt(
            app->function, localBinders, out);
        collectLibraryEqualitiesAt(
            app->argument, localBinders, out);
    }

std::vector<Elaborator::ContextEquality> Elaborator::collectContextEqualities(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/) {
        std::vector<ContextEquality> result;
        int N = static_cast<int>(localBinders.size());
        // Local hypotheses (cost 1) — scan last-bound first so the
        // most-recent equality wins on ties.
        for (int b = N - 1; b >= 0; --b) {
            int lift = N - b;
            ExpressionPointer hypInScope = liftBoundVariables(
                localBinders[b].type, lift, 0);
            ExpressionPointer hypReduced = weakHeadNormalForm(
                environment_, hypInScope);
            EqualityComponents components;
            try {
                components = extractEqualityComponents(
                    hypReduced, "local equality", 0);
            } catch (const ElaborateError&) { continue; }
            ContextEquality eq;
            eq.cost = 1;
            eq.source = "local binder " + localBinders[b].name;
            eq.carrierType = components.carrierType;
            eq.lhs = components.leftEndpoint;
            eq.rhs = components.rightEndpoint;
            eq.carrierLevel = components.carrierUniverseLevel;
            eq.proofExpr = makeBoundVariable(N - 1 - b);
            result.push_back(std::move(eq));
        }
        // Library lemmas matched against goal subexpressions
        // (cost 3) — walks Application subexpressions and queries
        // `lemmaIndex_` at each.
        collectLibraryEqualitiesAt(
            goalClosed, localBinders, result);
        return result;
    }

ExpressionPointer Elaborator::tryContextEqualityBridge(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line, int budget) {
        if (budget == 0) return nullptr;
        std::vector<ContextEquality> equalities =
            collectContextEqualities(
                goalClosed, localBinders, line);
        std::sort(equalities.begin(), equalities.end(),
            [](const ContextEquality& a, const ContextEquality& b) {
                return a.cost < b.cost;
            });
        for (const ContextEquality& eq : equalities) {
            // Try both rewrite directions:
            //   direction 0: replace rhs in goal with lhs — uses eq
            //     directly (transport: motive(lhs) → motive(rhs)).
            //   direction 1: replace lhs in goal with rhs — uses
            //     symm(eq) (transport: motive(rhs) → motive(lhs)).
            for (int direction = 0; direction < 2; ++direction) {
                // Each direction abstracts an occurrence and recurses into
                // autoProveClaim on the rewritten goal — the prover's most
                // expensive per-candidate work (this tactic dominated the
                // #19 thrash). Charge the budget (throws once exhausted).
                autoProveSpend(2);
                ExpressionPointer fromSide =
                    (direction == 0) ? eq.rhs : eq.lhs;
                ExpressionPointer toSide =
                    (direction == 0) ? eq.lhs : eq.rhs;
                int occurrences = 0;
                ExpressionPointer abstractedBody =
                    abstractStructuralOccurrence(
                        goalClosed, fromSide,
                        /*currentDepth=*/0, occurrences);
                if (occurrences == 0) continue;
                ExpressionPointer rewrittenGoal = substitute(
                    abstractedBody, 0, toSide);
                ExpressionPointer proofRewritten;
                try {
                    proofRewritten = autoProveClaim(
                        rewrittenGoal, localBinders,
                        line, budget - 1);
                } catch (const ElaborateError&) { continue; }
                  catch (const TypeError&) { continue; }
                ExpressionPointer motive = makeLambda(
                    "_rewriteHole",
                    eq.carrierType, abstractedBody);
                ExpressionPointer eqForTransport;
                ExpressionPointer transportLhs;
                ExpressionPointer transportRhs;
                if (direction == 0) {
                    eqForTransport = eq.proofExpr;
                    transportLhs = eq.lhs;
                    transportRhs = eq.rhs;
                } else {
                    eqForTransport = makeConstant(
                        "Equality.symmetry",
                        {eq.carrierLevel});
                    eqForTransport = makeApplication(
                        eqForTransport, eq.carrierType);
                    eqForTransport = makeApplication(
                        eqForTransport, eq.lhs);
                    eqForTransport = makeApplication(
                        eqForTransport, eq.rhs);
                    eqForTransport = makeApplication(
                        eqForTransport, eq.proofExpr);
                    transportLhs = eq.rhs;
                    transportRhs = eq.lhs;
                }
                ExpressionPointer call = makeConstant(
                    "Equality.transport_proposition",
                    {eq.carrierLevel});
                call = makeApplication(call, eq.carrierType);
                call = makeApplication(call, motive);
                call = makeApplication(call, transportLhs);
                call = makeApplication(call, transportRhs);
                call = makeApplication(call, eqForTransport);
                call = makeApplication(call, proofRewritten);
                return call;
            }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryConjunctionIntro(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        auto* outerApp = std::get_if<Application>(&goalOpened->node);
        if (!outerApp) return nullptr;
        auto* innerApp = std::get_if<Application>(
            &outerApp->function->node);
        if (!innerApp) return nullptr;
        auto* head = std::get_if<Constant>(&innerApp->function->node);
        if (!head || head->name != "And") return nullptr;
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer aClosed = closeOverLocalBinders(
            innerApp->argument, localBinders, N);
        ExpressionPointer bClosed = closeOverLocalBinders(
            outerApp->argument, localBinders, N);
        ExpressionPointer proofA;
        try {
            proofA = autoProveClaim(
                aClosed, localBinders, line);
        } catch (const ElaborateError&) { return nullptr; }
          catch (const TypeError&) { return nullptr; }
        ExpressionPointer proofB;
        try {
            proofB = autoProveClaim(
                bClosed, localBinders, line);
        } catch (const ElaborateError&) { return nullptr; }
          catch (const TypeError&) { return nullptr; }
        if (!environment_.lookup("And.introduction")) return nullptr;
        ExpressionPointer call = makeConstant(
            "And.introduction", {});
        call = makeApplication(call, aClosed);
        call = makeApplication(call, bClosed);
        call = makeApplication(call, proofA);
        call = makeApplication(call, proofB);
        return call;
    }

ExpressionPointer Elaborator::tryTransitivityBridge(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        auto* outerApp = std::get_if<Application>(&goalOpened->node);
        if (!outerApp) return nullptr;
        auto* innerApp = std::get_if<Application>(
            &outerApp->function->node);
        if (!innerApp) return nullptr;
        auto* head = std::get_if<Constant>(&innerApp->function->node);
        if (!head) return nullptr;
        std::string transitiveName = head->name + ".transitive";
        if (!environment_.lookup(transitiveName)) return nullptr;
        ExpressionPointer goalAOpened = innerApp->argument;
        ExpressionPointer goalCOpened = outerApp->argument;
        int N = static_cast<int>(localBinders.size());
        Context openedContext =
            buildContextFromLocalBinders(localBinders);

        // Collect hypothesis edges: (source, target, binderIdx) for
        // each local binder of type `head(_, _)`.
        struct HypEdge {
            ExpressionPointer source;
            ExpressionPointer target;
            int binderIdx;
        };
        std::vector<HypEdge> edges;
        for (int b = N - 1; b >= 0; --b) {
            int lift = N - b;
            ExpressionPointer hTypeOpened = openOverLocalBinders(
                liftBoundVariables(
                    localBinders[b].type, lift, 0),
                localBinders, N);
            auto* hOuter = std::get_if<Application>(
                &hTypeOpened->node);
            if (!hOuter) continue;
            auto* hInner = std::get_if<Application>(
                &hOuter->function->node);
            if (!hInner) continue;
            auto* hHead = std::get_if<Constant>(
                &hInner->function->node);
            if (!hHead || hHead->name != head->name) continue;
            edges.push_back(
                {hInner->argument, hOuter->argument, b});
        }
        if (edges.empty()) return nullptr;

        // BFS from goalA, target goalC.
        std::vector<ExpressionPointer> reached;
        std::vector<int> reachedEdge;
        std::vector<int> reachedPred;
        reached.push_back(goalAOpened);
        reachedEdge.push_back(-1);
        reachedPred.push_back(-1);
        int targetReachedIdx = -1;
        constexpr int MAX_DEPTH = 8;
        int frontierStart = 0;
        int frontierEnd = 1;
        for (int depth = 0;
             targetReachedIdx == -1 && depth < MAX_DEPTH;
             ++depth) {
            for (int i = frontierStart;
                 i < frontierEnd && targetReachedIdx == -1;
                 ++i) {
                ExpressionPointer current = reached[i];
                for (size_t e = 0; e < edges.size(); ++e) {
                    if (!isDefinitionallyEqual(
                            environment_, openedContext,
                            edges[e].source, current)) continue;
                    ExpressionPointer target = edges[e].target;
                    bool already = false;
                    for (auto& r : reached) {
                        if (isDefinitionallyEqual(
                                environment_, openedContext,
                                r, target)) {
                            already = true;
                            break;
                        }
                    }
                    if (already) continue;
                    reached.push_back(target);
                    reachedEdge.push_back(
                        static_cast<int>(e));
                    reachedPred.push_back(i);
                    if (isDefinitionallyEqual(
                            environment_, openedContext,
                            target, goalCOpened)) {
                        targetReachedIdx =
                            static_cast<int>(reached.size()) - 1;
                        break;
                    }
                }
            }
            frontierStart = frontierEnd;
            frontierEnd = static_cast<int>(reached.size());
            if (frontierStart == frontierEnd) break;
        }
        if (targetReachedIdx == -1) return nullptr;

        // Reconstruct path: list of edge indices from source to target.
        std::vector<int> pathEdges;
        {
            int idx = targetReachedIdx;
            while (idx > 0) {
                pathEdges.push_back(reachedEdge[idx]);
                idx = reachedPred[idx];
            }
            std::reverse(pathEdges.begin(), pathEdges.end());
        }
        if (pathEdges.empty()) return nullptr;

        // Single-edge path: the hypothesis IS the proof.
        if (pathEdges.size() == 1) {
            return makeBoundVariable(
                N - 1 - edges[pathEdges[0]].binderIdx);
        }

        // Multi-edge path: fold transitive applications. accumulator
        // accProof : H(goalA, accTarget) starts with the first edge.
        ExpressionPointer accProof = makeBoundVariable(
            N - 1 - edges[pathEdges[0]].binderIdx);
        ExpressionPointer accTarget = edges[pathEdges[0]].target;
        for (size_t i = 1; i < pathEdges.size(); ++i) {
            const HypEdge& nextEdge = edges[pathEdges[i]];
            ExpressionPointer nextProof = makeBoundVariable(
                N - 1 - nextEdge.binderIdx);
            ExpressionPointer combined = buildTransitiveCall(
                transitiveName,
                goalAOpened, accTarget, nextEdge.target,
                accProof, nextProof, localBinders);
            if (!combined) return nullptr;
            accProof = combined;
            accTarget = nextEdge.target;
        }
        return accProof;
    }

ExpressionPointer Elaborator::buildTransitiveCall(
        const std::string& transitiveName,
        ExpressionPointer aOpened,
        ExpressionPointer bOpened,
        ExpressionPointer cOpened,
        ExpressionPointer hAB,
        ExpressionPointer hBC,
        const std::vector<LocalBinder>& localBinders) {
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer aClosed = closeOverLocalBinders(
            aOpened, localBinders, N);
        ExpressionPointer bClosed = closeOverLocalBinders(
            bOpened, localBinders, N);
        ExpressionPointer cClosed = closeOverLocalBinders(
            cOpened, localBinders, N);
        for (int order = 0; order < 2; ++order) {
            ExpressionPointer call = makeConstant(
                transitiveName, {});
            call = makeApplication(call, aClosed);
            call = makeApplication(call, bClosed);
            call = makeApplication(call, cClosed);
            if (order == 0) {
                call = makeApplication(call, hAB);
                call = makeApplication(call, hBC);
            } else {
                call = makeApplication(call, hBC);
                call = makeApplication(call, hAB);
            }
            try {
                (void)inferTypeInLocalContext(
                    localBinders, call);
                return call;
            } catch (const TypeError&) { continue; }
              catch (const ElaborateError&) { continue; }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryAutoProveEqualityGoal(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        ExpressionPointer goalWhnf = weakHeadNormalForm(
            environment_, goalOpened);
        EqualityComponents components;
        try {
            components = extractEqualityComponents(
                goalWhnf, "auto-prove equality goal", line);
        } catch (const ElaborateError&) {
            return nullptr;
        }
        ExpressionPointer carrierClosed = closeOverLocalBinders(
            components.carrierType, localBinders,
            localBinders.size());
        ExpressionPointer leftClosed = closeOverLocalBinders(
            components.leftEndpoint, localBinders,
            localBinders.size());
        ExpressionPointer rightClosed = closeOverLocalBinders(
            components.rightEndpoint, localBinders,
            localBinders.size());
        try {
            return autoProveCalcStep(
                localBinders, leftClosed, rightClosed,
                carrierClosed, components.carrierUniverseLevel,
                goalClosed, line, 0);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
    }

ExpressionPointer Elaborator::trySymmetryFlip(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        if (symmetryFlipDepth_ > 0) return nullptr;
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer goalWhnf;
        try {
            goalWhnf = weakHeadNormalForm(environment_,
                openOverLocalBinders(goalClosed, localBinders, N));
        } catch (...) { return nullptr; }

        // Equality: `x = y`  ←  Equality.symmetry of `y = x`.
        bool isEquality = true;
        EqualityComponents comps;
        try {
            comps = extractEqualityComponents(
                goalWhnf, "symmetry flip", line);
        } catch (const ElaborateError&) { isEquality = false; }
          catch (const TypeError&) { isEquality = false; }
        if (isEquality) {
            ExpressionPointer carrier = closeOverLocalBinders(
                comps.carrierType, localBinders, N);
            ExpressionPointer x = closeOverLocalBinders(
                comps.leftEndpoint, localBinders, N);
            ExpressionPointer y = closeOverLocalBinders(
                comps.rightEndpoint, localBinders, N);
            ExpressionPointer flipped = makeApplication(makeApplication(
                makeApplication(makeConstant("Equality",
                    {comps.carrierUniverseLevel}), carrier), y), x);
            ExpressionPointer flippedProof;
            ++symmetryFlipDepth_;
            try {
                flippedProof = autoProveClaim(flipped, localBinders, line);
            } catch (const ElaborateError&) { flippedProof = nullptr; }
              catch (const TypeError&) { flippedProof = nullptr; }
            --symmetryFlipDepth_;
            if (!flippedProof) return nullptr;
            // Equality.symmetry.{u}(carrier, y, x, flippedProof) : x = y
            ExpressionPointer wrap = makeConstant(
                "Equality.symmetry", {comps.carrierUniverseLevel});
            for (ExpressionPointer a : {carrier, y, x, flippedProof}) {
                wrap = makeApplication(wrap, a);
            }
            return wrap;
        }

        // Generic symmetric relation: `R(x, y)`  ←  `<R>.symmetric` of
        // `R(y, x)`. Requires R applied to exactly two arguments and a
        // registered symmetry lemma; the wrapped term is type-checked
        // against the goal, so a wrong arg shape simply declines.
        auto* outerApp = std::get_if<Application>(&goalWhnf->node);
        if (!outerApp) return nullptr;
        auto* innerApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!innerApp) return nullptr;
        auto* head = std::get_if<Constant>(&innerApp->function->node);
        if (!head) return nullptr;
        std::string symName;
        for (const std::string& candidate :
             {head->name + ".symmetric", head->name + "_symmetric"}) {
            if (environment_.lookup(candidate)) {
                symName = candidate;
                break;
            }
        }
        if (symName.empty()) return nullptr;
        ExpressionPointer relation = closeOverLocalBinders(
            innerApp->function, localBinders, N);
        ExpressionPointer x = closeOverLocalBinders(
            innerApp->argument, localBinders, N);
        ExpressionPointer y = closeOverLocalBinders(
            outerApp->argument, localBinders, N);
        ExpressionPointer flipped = makeApplication(
            makeApplication(relation, y), x);
        ExpressionPointer flippedProof;
        ++symmetryFlipDepth_;
        try {
            flippedProof = autoProveClaim(flipped, localBinders, line);
        } catch (const ElaborateError&) { flippedProof = nullptr; }
          catch (const TypeError&) { flippedProof = nullptr; }
        --symmetryFlipDepth_;
        if (!flippedProof) return nullptr;
        // <R>.symmetric(y, x, flippedProof) : R(x, y) — verified below.
        ExpressionPointer wrap = makeConstant(symName);
        for (ExpressionPointer a : {y, x, flippedProof}) {
            wrap = makeApplication(wrap, a);
        }
        try {
            ExpressionPointer wrapType =
                inferTypeInLocalContext(localBinders, wrap);
            Context context = buildContextFromLocalBinders(localBinders);
            if (!isDefinitionallyEqual(environment_, context,
                    wrapType, goalWhnf)) {
                return nullptr;
            }
        } catch (...) { return nullptr; }
        return wrap;
    }

ExpressionPointer Elaborator::autoProveClaim(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line,
        int transportBudget) {
        // Tactic order is chosen to minimise total time, not to match
        // the docstring narrative above. The cheap shape-gated tactics
        // (equalityBattery, transitivityBridge, conjunctionIntro,
        // contradiction) run first because each does an O(1) head
        // check and bails on the wrong goal shape. After those, we
        // try contextFactMatch — empirically the highest-hit-rate
        // tactic (~10% per call on math-heavy files), so promoting
        // it past the per-call-expensive disjunctionIntro and
        // contextEqualityBridge skips those when a hypothesis or
        // library lemma already closes the goal.
        ++autoProveDepth_;
        struct DepthDecrement {
            int& d;
            ~DepthDecrement() { --d; }
        } decrementer{autoProveDepth_};

        // Arm the effort budget on the OUTERMOST claim (depth 0 -> 1) and
        // disarm it (and reset the trip flag) when that call unwinds, so
        // each top-level claim gets a fresh budget shared by all of its
        // recursive sub-proofs. See autoProveBudget_ (kernel_quirks #19).
        struct BudgetGuard {
            Elaborator& e;
            bool armedHere;
            ~BudgetGuard() {
                if (armedHere) {
                    e.autoProveBudgetActive_ = false;
                    e.autoProveBudgetTripped_ = false;
                }
            }
        };
        bool armedHere = false;
        if (autoProveDepth_ == 1 && autoProveBudgetLimit_ > 0
            && !autoProveBudgetActive_) {
            autoProveBudgetActive_ = true;
            autoProveBudgetTripped_ = false;
            autoProveStepSnapshot_ = kernelStepsSoFar();
            armedHere = true;
        }
        BudgetGuard budgetGuard{*this, armedHere};

        // The budget owner (the outermost armed frame) catches a raw
        // AutoProverBudgetError thrown by a hot loop deep in the search and
        // re-issues it with the goal + search suggestions, so every entry
        // path (calc step, bare `claim`, coercion, …) gets the actionable
        // "add `by`" message. Inner frames let it propagate untouched.
        if (armedHere) {
            ExpressionPointer proof;
            try {
                proof = autoProveClaimTactics(
                    goalClosed, localBinders, line, transportBudget);
            } catch (const AutoProverBudgetError&) {
                throwAutoProveBudgetExceeded(goalClosed, localBinders);
            }
            // Warning tier: a by-less step that DID close but cost more than
            // the warn threshold (in kernel reduction steps) is almost
            // always a hidden computation — an abstract-ring rearrangement
            // closed by the lemma-index diff matcher, a quotient-arithmetic
            // defeq, etc. It verifies, so this is a non-fatal nudge to make
            // it explicit (`by <reason>`), which the kernel then checks
            // ~instantly. Threshold overridable via MATH_AUTOPROVE_WARN
            // (0 disables); well below the hard budget so it fires first.
            if (proof) {
                uint64_t spent = kernelStepsSoFar() - autoProveStepSnapshot_;
                long long warnAt = autoProveWarnThresholdValue();
                if (warnAt > 0 && spent > (uint64_t)warnAt) {
                    std::cerr << "warning: " << moduleName_ << ":" << line
                        << ": expensive by-less proof step ("
                        << spent << " kernel-steps) — the auto-prover closed "
                        "it by search; add an explicit `by <reason>` so the "
                        "kernel checks it directly (much faster, and the "
                        "intent is recorded)\n";
                }
            }
            return proof;
        }
        return autoProveClaimTactics(
            goalClosed, localBinders, line, transportBudget);
    }

ExpressionPointer Elaborator::autoProveClaimTactics(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line,
        int transportBudget) {
        // Charge a baseline unit per claim so a deep recursive fan-out
        // (context-equality bridge / symmetry-flip recursing into the
        // prover) is bounded even when each individual call's loops are
        // short. The equality battery below — which runs autoProveCalcStep
        // (reflexivity conversion + diff walk + AC) — is the single most
        // expensive thing a leaf claim does, so a per-claim charge caps
        // how many such leaves the fan-out can spawn. Throws
        // AutoProverBudgetError once the kernel-step budget is exhausted.
        autoProveSpend(1);

        if (autoProveProfileEnabled_ && autoProveDepth_ == 1) {
            return autoProveClaimProfiling(
                goalClosed, localBinders, line, transportBudget);
        }

        {
            ExpressionPointer attempt = runTactic("equalityBattery",
                [&] { return tryAutoProveEqualityGoal(
                    goalClosed, localBinders, line); });
            if (attempt) return attempt;
        }

        {
            ExpressionPointer attempt = runTactic("transitivityBridge",
                [&] { return tryTransitivityBridge(
                    goalClosed, localBinders, line); });
            if (attempt) return attempt;
        }

        {
            ExpressionPointer attempt = runTactic("conjunctionIntro",
                [&] { return tryConjunctionIntro(
                    goalClosed, localBinders, line); });
            if (attempt) return attempt;
        }

        {
            ExpressionPointer attempt = runTactic("contradiction",
                [&] { return tryContradiction(
                    goalClosed, localBinders, line); });
            if (attempt) return attempt;
        }

        // From here on the tactics are per-call expensive (full library
        // scans, recursive sub-proofs). Each charges the effort budget in
        // its hot loop via autoProveSpend(), which throws
        // AutoProverBudgetError the moment the kernel-step budget is
        // exhausted — that exception propagates straight to the proof-step
        // dispatch (it is not an ElaborateError, so the speculative
        // catches below don't swallow it).

        // Context fact match — unified local-hypothesis + library
        // scan. Iterates all in-scope facts (local binders and
        // applicable library declarations) by cost, trying
        // autoFillHintForClaim on each. Expensive per call (~4 ms
        // average on math-heavy goals) but high hit rate, so it
        // pays for itself by short-circuiting the equally expensive
        // disjunctionIntro / contextEqualityBridge below.
        {
            ExpressionPointer attempt = runTactic("contextFactMatch",
                [&] { return tryContextFactMatch(
                    goalClosed, localBinders, line); });
            if (attempt) return attempt;
        }

        // Disjunction introduction — when the goal is `Or(A, B)`,
        // try proving A; if that fails, try B. Left-biased.
        {
            ExpressionPointer attempt = runTactic("disjunctionIntro",
                [&] { return tryDisjunctionIntro(
                    goalClosed, localBinders, line); });
            if (attempt) return attempt;
        }

        // contextEqualityBridge: opt-out via MATH_DISABLE_CTX_EQ_BRIDGE=1.
        // The profiler showed it wins only 16 of 217 outermost claim
        // sites across the library while costing ~20 s total. Disabled
        // by default to measure the saving; opt back in when you want
        // it. Sites that need it surface as "no in-scope hypothesis
        // matches structurally…" claim errors.
        static const bool ctxEqBridgeDisabled = [] {
            const char* f = std::getenv("MATH_DISABLE_CTX_EQ_BRIDGE");
            return f && f[0] != '\0' && f[0] != '0';
        }();
        if (!ctxEqBridgeDisabled) {
            ExpressionPointer attempt = runTactic("contextEqualityBridge",
                [&] { return tryContextEqualityBridge(
                    goalClosed, localBinders,
                    line, transportBudget); });
            if (attempt) return attempt;
        } else {
            (void)transportBudget;
        }

        // Quotient `exact` bridge — last resort (only reached once the
        // cheaper strategies miss, so its per-goal scan rarely runs): goal
        // `R(a, b)` closes from an in-scope `mk a = mk b` fact via
        // Quotient.exact, so proofs never name it. Placed before symmetryFlip
        // so a flipped fact (`mk b = mk a`) is caught when symmetryFlip
        // recurses on the flipped goal `R(b, a)`.
        {
            ExpressionPointer attempt = runTactic("quotientExactBridge",
                [&] { return tryQuotientExactBridge(
                    goalClosed, localBinders); });
            if (attempt) return attempt;
        }

        // Symmetry flip — true last resort: `x = y` (or symmetric
        // `R(x, y)`) from a fact stated the other way. Placed last so the
        // bridge (which already rewrites equalities) closes the common
        // equality cases first; this is what uniquely catches a symmetric
        // NON-equality relation `R`. Recursively runs the prover on the
        // flipped goal, so it must come after everything cheaper.
        {
            ExpressionPointer attempt = runTactic("symmetryFlip",
                [&] { return trySymmetryFlip(
                    goalClosed, localBinders, line); });
            if (attempt) return attempt;
        }

        throwElaborate(
            "claim `"
            + prettyPrintInLocalScope(goalClosed, localBinders)
            + "`: no in-scope hypothesis matches structurally, no "
            "equality battery (reflexivity / diff / ring) closes the "
            "goal, no transitivity chain reaches the goal, no "
            "conjunction split decomposes it, no in-scope "
            "contradiction lets us close it, no library theorem "
            "with this conclusion shape applies, and no context "
            "equality lets us rewrite to a provable form — add "
            "`by <lemma>` to specify"
            + searchSuggestions(goalClosed, localBinders));
    }

void Elaborator::throwAutoProveBudgetExceeded(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders) {
        std::string goal;
        try {
            goal = prettyPrintInLocalScope(goalClosed, localBinders);
        } catch (...) { goal = "<goal>"; }
        std::string hints;
        try {
            hints = searchSuggestions(goalClosed, localBinders);
        } catch (...) { hints.clear(); }
        // Throw the dedicated budget exception (NOT an ElaborateError) so
        // the rich message likewise survives the speculative catches and
        // reaches the proof-step dispatch / driver intact.
        throw AutoProverBudgetError(
            "claim `" + goal
            + "`: the auto-prover gave up after exhausting its effort "
            "budget (it explored too far without closing the goal — most "
            "often because an endpoint mentions a recursive definition "
            "that is expensive to unfold). Add an explicit `by <reason>` "
            "to name the lemma / proof so the kernel can check it by "
            "definitional equality instead of the prover searching for "
            "it. (Raise or disable the bound with MATH_AUTOPROVE_BUDGET "
            "if you believe the step really should auto-close.)"
            + hints);
    }

ExpressionPointer Elaborator::autoProveClaimProfiling(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line,
        int transportBudget) {
        AutoProveRow row;
        row.moduleName = moduleName_;
        row.line = line;
        row.goalSize = countExpressionNodes(goalClosed);
        row.goalHead = goalHeadName(goalClosed);
        ExpressionPointer firstSuccess = nullptr;

        auto runProfiled = [&](const char* tacticName,
                               auto&& fn) {
            AutoProveAttempt attempt;
            attempt.tacticName = tacticName;
            attempt.succeeded = false;
            attempt.micros = 0;
            // Reset contextFactMatch's per-call profiling fields so
            // we don't carry winners over from earlier tactics.
            lastContextFactWinner_.clear();
            lastContextFactCandidateCount_ = 0;
            auto t0 = std::chrono::steady_clock::now();
            ExpressionPointer result = nullptr;
            try {
                result = fn();
            } catch (const ElaborateError&) {
                result = nullptr;
            } catch (const TypeError&) {
                result = nullptr;
            }
            auto t1 = std::chrono::steady_clock::now();
            attempt.micros =
                std::chrono::duration_cast<std::chrono::microseconds>(
                    t1 - t0).count();
            attempt.succeeded = (result != nullptr);
            if (std::string(tacticName) == "contextFactMatch") {
                attempt.winner = lastContextFactWinner_;
                attempt.candidatesTried =
                    lastContextFactCandidateCount_;
            }
            // First success becomes the returned proof — but we keep
            // running later tactics for the comparison data.
            if (result && !firstSuccess) {
                firstSuccess = result;
                if (row.winningTactic.empty()) {
                    row.winningTactic = tacticName;
                }
            }
            row.attempts.push_back(std::move(attempt));
            // Also feed the global tactic-timing aggregate so the
            // existing [tactic] summary still reports invocations and
            // successes consistently across profiling and non-profiling
            // runs. Otherwise the headline numbers would diverge.
            auto& bucket = tacticStats_[tacticName];
            ++bucket.invocations;
            if (result) ++bucket.successes;
            bucket.totalMicros += attempt.micros;
        };

        runProfiled("equalityBattery", [&] {
            return tryAutoProveEqualityGoal(
                goalClosed, localBinders, line);
        });
        runProfiled("transitivityBridge", [&] {
            return tryTransitivityBridge(
                goalClosed, localBinders, line);
        });
        runProfiled("conjunctionIntro", [&] {
            return tryConjunctionIntro(
                goalClosed, localBinders, line);
        });
        runProfiled("contradiction", [&] {
            return tryContradiction(
                goalClosed, localBinders, line);
        });
        runProfiled("contextFactMatch", [&] {
            return tryContextFactMatch(
                goalClosed, localBinders, line);
        });
        runProfiled("disjunctionIntro", [&] {
            return tryDisjunctionIntro(
                goalClosed, localBinders, line);
        });
        runProfiled("contextEqualityBridge", [&] {
            return tryContextEqualityBridge(
                goalClosed, localBinders, line, transportBudget);
        });

        autoProveRows_.push_back(std::move(row));

        if (firstSuccess) return firstSuccess;
        throwElaborate(
            "claim `"
            + prettyPrintInLocalScope(goalClosed, localBinders)
            + "`: no in-scope hypothesis matches structurally, no "
            "equality battery (reflexivity / diff / ring) closes the "
            "goal, no transitivity chain reaches the goal, no "
            "conjunction split decomposes it, no in-scope "
            "contradiction lets us close it, no library theorem "
            "with this conclusion shape applies, and no context "
            "equality lets us rewrite to a provable form — add "
            "`by <lemma>` to specify"
            + searchSuggestions(goalClosed, localBinders));
    }

std::string Elaborator::goalHeadName(ExpressionPointer expression) {
        ExpressionPointer head = expression;
        while (auto* app = std::get_if<Application>(&head->node)) {
            head = app->function;
        }
        if (auto* c = std::get_if<Constant>(&head->node)) {
            return c->name;
        }
        if (std::holds_alternative<Sort>(head->node)) return "<sort>";
        if (std::holds_alternative<Pi>(head->node)) return "<pi>";
        if (std::holds_alternative<Lambda>(head->node)) return "<lambda>";
        if (std::holds_alternative<Let>(head->node)) return "<let>";
        if (std::holds_alternative<BoundVariable>(head->node)) return "<bv>";
        if (std::holds_alternative<FreeVariable>(head->node)) return "<fv>";
        return "<?>";
    }


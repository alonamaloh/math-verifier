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

// Whether the auto-prover restricts its unprompted library tier to
// `automatic`-tagged (or same-module) declarations. On by default now that
// the library's foundational lemmas are tagged; opt OUT with
// MATH_AUTOMATIC=0 (escape hatch for debugging / bisecting).
bool automaticRestrictEnabled() {
    static const bool v = [] {
        const char* e = std::getenv("MATH_AUTOMATIC");
        return !(e && e[0] == '0');
    }();
    return v;
}

// Cheap structural fingerprint of an expression's conclusion spine: the head
// constant name plus the head-constant name of each top-level argument (empty
// for a non-constant-headed argument). No WHNF, no allocation beyond the small
// vectors — used only to ORDER auto-prover candidates, never to reject them.
void spineHeadAndArgHeads(ExpressionPointer expression,
                          std::string& head,
                          std::vector<std::string>& argHeads) {
    std::vector<ExpressionPointer> args;
    ExpressionPointer cursor = expression;
    while (auto* app = std::get_if<Application>(&cursor->node)) {
        args.push_back(app->argument);
        cursor = app->function;
    }
    if (auto* constant = std::get_if<Constant>(&cursor->node)) {
        head = constant->name;
    } else {
        head.clear();
    }
    argHeads.clear();
    for (auto iter = args.rbegin(); iter != args.rend(); ++iter) {
        argHeads.push_back(applicationHeadConstantName(*iter));
    }
}

// Similarity of a candidate fact's conclusion to the goal: 0 when the heads
// differ (so a head-mismatched fact keeps its tier's recency order), else
// 1 + (number of argument positions whose head constants agree). Peels the
// fact type's Pi chain to its conclusion first.
int structuralSimilarityScore(const std::string& goalHead,
                              const std::vector<std::string>& goalArgHeads,
                              ExpressionPointer factType) {
    if (goalHead.empty()) return 0;
    ExpressionPointer cursor = factType;
    while (auto* pi = std::get_if<Pi>(&cursor->node)) cursor = pi->codomain;
    std::string factHead;
    std::vector<std::string> factArgHeads;
    spineHeadAndArgHeads(cursor, factHead, factArgHeads);
    if (factHead != goalHead) return 0;
    int score = 1;
    size_t n = std::min(goalArgHeads.size(), factArgHeads.size());
    for (size_t i = 0; i < n; ++i) {
        if (!goalArgHeads[i].empty() && goalArgHeads[i] == factArgHeads[i]) {
            ++score;
        }
    }
    return score;
}
}  // namespace

namespace {
// Effort cap (kernel reduction steps) for the speculative re-proof in the
// redundancy checks. Deliberately LOW: a hint is "redundant" only when the
// by-less re-proof is near-instant, so the check flags noise hints (a step
// the prover closes trivially anyway) and stays silent on hints that save
// the prover real search — otherwise cleanup round-trips (drop a "redundant"
// hint, then the step turns into an expensive by-less proof and the hint has
// to go back). Overridable via MATH_REDUNDANT_BUDGET (0 disables → use the
// default auto-prove budget).
long long redundancyBudgetValue() {
    static long long cached = [] {
        if (const char* w = std::getenv("MATH_REDUNDANT_BUDGET")) {
            char* end = nullptr;
            long long v = std::strtoll(w, &end, 10);
            if (end != w && v >= 0) return v;
        }
        return 1000LL;
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
        // WHNF so a folded `Not(P)` (the transparent definition
        // `P → False`) shows its `Pi` head — otherwise the `Not`/`P`
        // pair search below sees only an `Application` and misses it.
        ExpressionPointer lastTypeOpened = weakHeadNormalForm(
            environment_,
            openOverLocalBinders(
                liftBoundVariables(
                    localBinders[lastIdx].type, lastLift, 0),
                localBinders, N));
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
            ExpressionPointer otherType = weakHeadNormalForm(
                environment_,
                openOverLocalBinders(
                    liftBoundVariables(
                        localBinders[other].type, lift, 0),
                    localBinders, N));
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

std::vector<Elaborator::ContextFact> Elaborator::collectLocalBinderFacts(
        const std::vector<LocalBinder>& localBinders) {
        // B1 tier-0 stage 1a: exact-context memo (see the cache's
        // declaration comment). Consecutive claims in one block hit
        // the same context repeatedly; the rebuild below is what the
        // ε-δ profiling showed dominating.
        uint64_t cacheKey = 1469598103934665603ull;
        for (const LocalBinder& binder : localBinders) {
            cacheKey ^= binder.type ? binder.type->hash : 0;
            cacheKey *= 1099511628211ull;
        }
        auto cached = localFactCache_.find(cacheKey);
        if (cached != localFactCache_.end()
            && cached->second.binderTypes.size() == localBinders.size()) {
            bool identical = true;
            for (size_t b = 0; b < localBinders.size(); ++b) {
                if (cached->second.binderTypes[b].get()
                        != localBinders[b].type.get()) {
                    identical = false;
                    break;
                }
            }
            if (identical) return cached->second.facts;
        }
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
        // Conjunction elimination: a hypothesis `A ∧ B` makes A and B
        // available as facts in their own right — a mathematician just *has*
        // both, and never "projects a pair". Worklist so nested conjunctions
        // fully decompose.
        for (size_t cursor = 0; cursor < facts.size() && cursor < 4096;
             ++cursor) {
            ExpressionPointer conjunction = weakHeadNormalForm(
                environment_, facts[cursor].type);
            auto* outerApp =
                std::get_if<Application>(&conjunction->node);
            if (!outerApp) continue;
            auto* innerApp =
                std::get_if<Application>(&outerApp->function->node);
            if (!innerApp) continue;
            auto* head =
                std::get_if<Constant>(&innerApp->function->node);
            if (!head || head->name != "And") continue;
            ExpressionPointer leftType = innerApp->argument;   // A
            ExpressionPointer rightType = outerApp->argument;  // B
            ExpressionPointer proof = facts[cursor].proofTerm;
            long long childCost = facts[cursor].cost + 1;
            std::string childSource = facts[cursor].source;
            ContextFact leftFact;
            leftFact.cost = childCost;
            leftFact.source = childSource + " (∧-left)";
            leftFact.proofTerm = makeApplication(makeApplication(
                makeApplication(makeConstant("And.left", {}),
                    leftType), rightType), proof);
            leftFact.type = leftType;
            facts.push_back(std::move(leftFact));
            ContextFact rightFact;
            rightFact.cost = childCost;
            rightFact.source = childSource + " (∧-right)";
            rightFact.proofTerm = makeApplication(makeApplication(
                makeApplication(makeConstant("And.right", {}),
                    leftType), rightType), proof);
            rightFact.type = rightType;
            facts.push_back(std::move(rightFact));
        }
        if (localFactCache_.size() >= 512) {
            localFactCache_.clear();
        }
        LocalFactCacheEntry entry;
        entry.binderTypes.reserve(localBinders.size());
        for (const LocalBinder& binder : localBinders) {
            entry.binderTypes.push_back(binder.type);
        }
        entry.facts = facts;
        localFactCache_[cacheKey] = std::move(entry);
        return facts;
}

ExpressionPointer Elaborator::tryLocalFactExactMatch(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders) {
        // BASE binders only — no conjunction-leg decomposition (which WHNFs
        // every binder type and would tax this per-goal fast path). A goal
        // that equals a leg is still caught later by contextFactMatch; the
        // payoff here is a goal that IS a whole in-scope fact (e.g. a claimed
        // `IsCommutativeRing(…)`), matched as a unit before conjunctionIntro
        // decomposes it. Lift each binder's type to the goal's depth and
        // compare syntactically (cheap: structurallyEqual bails on head
        // mismatch). Most-recent binder first.
        int N = static_cast<int>(localBinders.size());
        for (int b = N - 1; b >= 0; --b) {
            ExpressionPointer factType = liftBoundVariables(
                localBinders[b].type, N - b, 0);
            if (structurallyEqual(factType, goalClosed)) {
                return makeBoundVariable(N - 1 - b);
            }
        }
        return nullptr;
}

std::vector<Elaborator::ContextFact> Elaborator::collectContextFacts(
        ExpressionPointer /*goalClosed*/,
        const std::vector<LocalBinder>& localBinders,
        uint64_t goalHash,
        uint64_t goalHashUnreduced) {
        // Local binders + their conjunction legs (cost 1+). Shared with the
        // lemma side-condition discharge path so both see the same facts.
        // Kept BEFORE the cite-only cutoff: this is local context, not a
        // library scan, so it stays on under cite-only.
        std::vector<ContextFact> facts = collectLocalBinderFacts(localBinders);
        // Cite-only mode: stop here — local hypotheses only. The global
        // library scan below is exactly the shotgun auto-search we disable,
        // so an unproven goal must be closed by an explicit `by L`.
        if (citeOnly_) return facts;
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
            // The `sorry` axioms (`Internal.sorry.{u}`,
            // `Internal.sorry_proposition`) inhabit EVERY type /
            // proposition — they exist solely as the target of the explicit
            // `sorry` keyword. They must never be reachable by proof SEARCH,
            // or the auto-prover would silently discharge any goal it cannot
            // otherwise close with an unsound `sorry` (e.g. proving
            // `0 ≠ 0`, hence `False`). Keep them out of the candidate pool.
            if (name.rfind("Internal.sorry", 0) == 0) continue;
            const auto& declaration = entry.second;
            ExpressionPointer declarationType;
            size_t universeParamCount = 0;
            // Automatic-visibility filter. A Definition/Axiom from another
            // module is in the unprompted pool only if it is `automatic`;
            // declarations of the current module are always visible (the
            // ".c-file interior"), as are constructors (fundamental, few,
            // no syntax to tag). Meatier imports need an explicit `by`.
            bool automaticOk = true;
            if (auto* def = std::get_if<Definition>(&declaration)) {
                declarationType = def->type;
                universeParamCount = def->universeParameters.size();
                automaticOk = def->automatic
                    || moduleDeclarationNames_.count(name);
            } else if (auto* ax = std::get_if<Axiom>(&declaration)) {
                declarationType = ax->type;
                universeParamCount = ax->universeParameters.size();
                automaticOk = ax->automatic
                    || moduleDeclarationNames_.count(name);
            } else if (auto* ctor =
                           std::get_if<Constructor>(&declaration)) {
                declarationType = ctor->type;
                universeParamCount = ctor->universeParameters.size();
            } else {
                continue;
            }
            if (automaticRestrictEnabled() && !automaticOk) continue;
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
        // Score each candidate by structural similarity to the goal, then
        // order by (cost asc, score desc). Within a cost tier the candidate
        // whose conclusion shares the goal's head + argument heads is tried
        // first — on a hypothesis-heavy goal the defeq winner is usually one
        // such match buried behind a run of head-compatible near-misses
        // (other equalities/inequalities), so this turns ~N failed attempts
        // before the win into ~1. Stable so recency order is the final
        // tiebreak (collectLocalBinderFacts emits most-recent first).
        {
            std::string goalHead;
            std::vector<std::string> goalArgHeads;
            spineHeadAndArgHeads(goalClosed, goalHead, goalArgHeads);
            for (ContextFact& fact : facts) {
                fact.score = structuralSimilarityScore(
                    goalHead, goalArgHeads, fact.type);
            }
        }
        std::stable_sort(facts.begin(), facts.end(),
            [](const ContextFact& a, const ContextFact& b) {
                if (a.cost != b.cost) return a.cost < b.cost;
                return a.score > b.score;
            });
        // Reset profiling fields each call — only meaningful when
        // autoProveProfileEnabled_, but the writes are cheap.
        lastContextFactWinner_.clear();
        lastContextFactCandidateCount_ = 0;
        int triedCount = 0;
        // Gate the citation premise-discharge's defeq fallback off for the
        // duration of this speculative scan (restored on exit): it is an
        // explicit-citation convenience, too costly to run per candidate here.
        bool savedSpeculativeScan = inSpeculativeContextScan_;
        inSpeculativeContextScan_ = true;
        struct ScanGuard {
            bool& flag; bool saved;
            ~ScanGuard() { flag = saved; }
        } scanGuard{inSpeculativeContextScan_, savedSpeculativeScan};
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
            if (!result && !citeOnly_) {
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
                lastWinningDetail_ = fact.source;
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
        // Local hypotheses (cost 1) and their conjunction legs — the SAME
        // facts the auto-prover and side-condition discharge see, via the
        // shared `collectLocalBinderFacts`. A hypothesis `A ∧ B` makes its
        // equality legs available to rewrite with (a mathematician who has
        // `… ∧ x = y` just *has* `x = y`); a fact whose type isn't an
        // equality is simply skipped.
        for (const ContextFact& fact : collectLocalBinderFacts(localBinders)) {
            EqualityComponents components;
            try {
                components = extractEqualityComponents(
                    weakHeadNormalForm(environment_, fact.type),
                    "local equality", 0);
            } catch (const ElaborateError&) { continue; }
            ContextEquality eq;
            eq.cost = fact.cost;
            eq.source = fact.source;
            eq.carrierType = components.carrierType;
            eq.lhs = components.leftEndpoint;
            eq.rhs = components.rightEndpoint;
            eq.carrierLevel = components.carrierUniverseLevel;
            eq.proofExpr = fact.proofTerm;
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
        // Two passes (cheap before expensive): pass 0 closes a rewritten goal
        // ONLY via the bounded-defeq reflexivity check above — no recursive
        // prove — so the equation whose rewrite makes the goal reflexive is
        // found cheaply, before any other equation's rewrite drags the full
        // recursive search. Pass 1 is the original recursive behaviour, run
        // only if pass 0 found nothing, so proofs that genuinely need the
        // search are unaffected.
        for (int pass = 0; pass < 2; ++pass) {
          bool fastOnly = (pass == 0);
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
                // Cheap close: if the rewrite left a definitionally-reflexive
                // goal (often the case for the RIGHT equation — e.g. rewriting
                // `to_rational(a+b)` to `to_rational a + to_rational b` makes
                // the two sides defeq), close it by reflexivity with a bounded
                // defeq probe and NO recursive prover call. The reflexivity is
                // re-checked at full fuel by the kernel, so a bounded false
                // positive cannot slip through.
                {
                    EqualityComponents rc;
                    bool plain = true;
                    try {
                        rc = extractEqualityComponents(
                            rewrittenGoal,
                            "context-equality bridge fast close", line);
                    } catch (const ElaborateError&) { plain = false; }
                      catch (const TypeError&) { plain = false; }
                    if (plain) {
                        int N = static_cast<int>(localBinders.size());
                        bool refl = structurallyEqual(
                            rc.leftEndpoint, rc.rightEndpoint);
                        if (!refl) {
                            try {
                                refl = isDefinitionallyEqual(
                                    environment_,
                                    buildContextFromLocalBinders(localBinders),
                                    openOverLocalBinders(
                                        rc.leftEndpoint, localBinders, N),
                                    openOverLocalBinders(
                                        rc.rightEndpoint, localBinders, N),
                                    kDefeqProbeFuel);
                            } catch (...) { refl = false; }
                        }
                        if (refl) {
                            proofRewritten = makeApplication(
                                makeApplication(
                                    makeConstant("reflexivity",
                                        {rc.carrierUniverseLevel}),
                                    rc.carrierType),
                                rc.leftEndpoint);
                        }
                    }
                }
                if (!proofRewritten) {
                    // Pass 0 does the cheap close ONLY — let a later equation
                    // (or pass 1) handle anything that needs the real search.
                    if (fastOnly) continue;
                    try {
                        proofRewritten = autoProveClaim(
                            rewrittenGoal, localBinders,
                            line, budget - 1);
                    } catch (const ElaborateError&) { continue; }
                      catch (const TypeError&) { continue; }
                }
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
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryConjunctionIntro(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        // WHNF the goal so one headed by a DEFINITION that unfolds to `A ∧ B`
        // — e.g. `is_gcd(g, a, b)` — is recognised as a conjunction and
        // assembled from its legs. This mirrors the decomposition side, which
        // already WHNFs before reading the `And` head, so `A ∧ B ∧ C` can be
        // proved by proving `A`, `B`, `C` even when the goal wears a
        // definition name. (`And` is an inductive, so it survives WHNF; a
        // genuinely non-conjunction goal reduces to a different head and we
        // bail, exactly as before.)
        ExpressionPointer goalWhnf = weakHeadNormalForm(
            environment_, goalOpened);
        auto* outerApp = std::get_if<Application>(&goalWhnf->node);
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

        // Collect hypothesis edges: (source, target, proof) for each local
        // fact of type `head(_, _)`. Drawn from `collectLocalBinderFacts` so a
        // conjunction hypothesis `(a R b) ∧ …` contributes its `a R b` leg as
        // an edge (proof = `And.left`/`And.right` projection), exactly like a
        // separately-stated `a R b` hypothesis.
        struct HypEdge {
            ExpressionPointer source;  // opened
            ExpressionPointer target;  // opened
            ExpressionPointer proof;   // closed at depth N
        };
        std::vector<HypEdge> edges;
        for (const ContextFact& fact : collectLocalBinderFacts(localBinders)) {
            ExpressionPointer hTypeOpened;
            try {
                hTypeOpened = openOverLocalBinders(fact.type, localBinders, N);
            } catch (const TypeError&) {
                continue;
            }
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
                {hInner->argument, hOuter->argument, fact.proofTerm});
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

        // Single-edge path: the fact IS the proof.
        if (pathEdges.size() == 1) {
            return edges[pathEdges[0]].proof;
        }

        // Multi-edge path: fold transitive applications. accumulator
        // accProof : H(goalA, accTarget) starts with the first edge.
        ExpressionPointer accProof = edges[pathEdges[0]].proof;
        ExpressionPointer accTarget = edges[pathEdges[0]].target;
        for (size_t i = 1; i < pathEdges.size(); ++i) {
            const HypEdge& nextEdge = edges[pathEdges[i]];
            ExpressionPointer nextProof = nextEdge.proof;
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
            {
                // RAII: an AutoProverBudgetError sails past the catches
                // by design and must not leak the depth increment (a
                // leaked increment disables symmetry flips for the rest
                // of the module).
                struct FlipDepthGuard {
                    int& d;
                    FlipDepthGuard(int& depth) : d(depth) { ++d; }
                    ~FlipDepthGuard() { --d; }
                } flipGuard{symmetryFlipDepth_};
                try {
                    flippedProof = autoProveClaim(flipped, localBinders, line);
                } catch (const ElaborateError&) { flippedProof = nullptr; }
                  catch (const TypeError&) { flippedProof = nullptr; }
            }
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
        {
            struct FlipDepthGuard {
                int& d;
                FlipDepthGuard(int& depth) : d(depth) { ++d; }
                ~FlipDepthGuard() { --d; }
            } flipGuard{symmetryFlipDepth_};
            try {
                flippedProof = autoProveClaim(flipped, localBinders, line);
            } catch (const ElaborateError&) { flippedProof = nullptr; }
              catch (const TypeError&) { flippedProof = nullptr; }
        }
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
        // Hard recursion bound. The kernel-step budget bounds WORK, not
        // FRAME DEPTH: a search whose levels are cheap (or whose budget
        // isn't armed) can otherwise nest prover frames until the stack
        // overflows (observed as SIGSEGV with kernel caches disabled).
        // Real searches resolve within a handful of levels; 64 is far
        // beyond any legitimate chain.
        if (autoProveDepth_ > 64) {
            return nullptr;
        }

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
            lastWinningTactic_.clear();
            lastWinningDetail_.clear();
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
                    std::string winnerHint = expensiveStepWinnerHint();
                    if (autoProveCallerLabel_.empty()) {
                        std::cerr << "warning: " << moduleName_ << ":"
                            << line
                            << ": expensive by-less proof step ("
                            << spent << " kernel-steps) — the auto-prover "
                            "closed it by search" << winnerHint
                            << "; add an explicit `by <reason>` so the "
                            "kernel checks it directly "
                            "(much faster, and the intent is recorded)\n";
                    } else {
                        std::cerr << "warning: " << moduleName_ << ":"
                            << line
                            << ": expensive proof search ("
                            << spent << " kernel-steps) inside "
                            << autoProveCallerLabel_
                            << " — the hint made the prover search; prefer "
                            "`since <fact>` or a more direct hint so the "
                            "kernel checks the step directly\n";
                    }
                }
            }
            return proof;
        }
        return autoProveClaimTactics(
            goalClosed, localBinders, line, transportBudget);
    }

ExpressionPointer Elaborator::tryLocalEqualityLeaf(
        ExpressionPointer left, ExpressionPointer right,
        ExpressionPointer carrierType, LevelPointer carrierLevel,
        const std::vector<LocalBinder>& localBinders, int line) {
        int N = static_cast<int>(localBinders.size());
        auto context = buildContextFromLocalBinders(localBinders);
        ExpressionPointer leftOpened = openOverLocalBinders(left, localBinders, N);
        ExpressionPointer rightOpened =
            openOverLocalBinders(right, localBinders, N);
        auto defeq = [&](ExpressionPointer a, ExpressionPointer b) -> bool {
            try {
                return isDefinitionallyEqual(
                    environment_, context, a, b, kDefeqProbeFuel);
            } catch (...) { return false; }
        };
        auto eqType = [&](ExpressionPointer x, ExpressionPointer y) {
            ExpressionPointer e = makeConstant("Equality", {carrierLevel});
            e = makeApplication(std::move(e), carrierType);
            e = makeApplication(std::move(e), x);
            e = makeApplication(std::move(e), y);
            return e;
        };
        auto transitivity = [&](ExpressionPointer x, ExpressionPointer y,
                                ExpressionPointer z, ExpressionPointer p,
                                ExpressionPointer q) {
            ExpressionPointer t = makeConstant(
                "Equality.transitivity", {carrierLevel});
            t = makeApplication(std::move(t), carrierType);
            t = makeApplication(std::move(t), x);
            t = makeApplication(std::move(t), y);
            t = makeApplication(std::move(t), z);
            t = makeApplication(std::move(t), std::move(p));
            t = makeApplication(std::move(t), std::move(q));
            return t;
        };
        // Scan local hypotheses last-bound-first (most recent wins on ties),
        // mirroring collectContextEqualities — but local ONLY for the primary
        // match (no library scan there).
        for (int b = N - 1; b >= 0; --b) {
            autoProveSpend(1);
            int lift = N - b;
            ExpressionPointer hypReduced = weakHeadNormalForm(
                environment_,
                liftBoundVariables(localBinders[b].type, lift, 0));
            EqualityComponents c;
            try {
                c = extractEqualityComponents(
                    hypReduced, "structuralDiff local leaf", 0);
            } catch (const ElaborateError&) { continue; }
            ExpressionPointer proofRef = makeBoundVariable(N - 1 - b);
            // Try the fact in both orientations: `lhs = rhs` (proofRef) and
            // `rhs = lhs` (symmetry proofRef). In each, the oriented LHS must
            // match the leaf's left under defeq.
            for (int orient = 0; orient < 2; ++orient) {
                ExpressionPointer ol =
                    (orient == 0) ? c.leftEndpoint : c.rightEndpoint;
                ExpressionPointer orr =
                    (orient == 0) ? c.rightEndpoint : c.leftEndpoint;
                if (!defeq(openOverLocalBinders(ol, localBinders, N),
                           leftOpened)) {
                    continue;
                }
                ExpressionPointer op;
                if (orient == 0) {
                    op = proofRef;
                } else {
                    ExpressionPointer s = makeConstant(
                        "Equality.symmetry", {c.carrierUniverseLevel});
                    s = makeApplication(std::move(s), c.carrierType);
                    s = makeApplication(std::move(s), c.leftEndpoint);
                    s = makeApplication(std::move(s), c.rightEndpoint);
                    s = makeApplication(std::move(s), proofRef);
                    op = std::move(s);
                }
                // Exact (defeq) RHS match: the oriented proof already has the
                // goal type up to defeq.
                if (defeq(openOverLocalBinders(orr, localBinders, N),
                          rightOpened)) {
                    return op;
                }
                // RHS differs (e.g. the opaque `successor(k)` vs `1+k` gap):
                // bridge `orr = right` and chain by transitivity. The gap is
                // a numeral/arithmetic normalisation, so the bridge goes to
                // the equality battery (which runs `ring`), NOT a fact scan —
                // but on the SMALL bridge term it is cheap, unlike running the
                // battery on the whole step. Only reached once the LHS already
                // matched a local hypothesis, so it is rare.
                ExpressionPointer bridge = tryAutoProveEqualityGoal(
                    eqType(orr, right), localBinders, line);
                if (bridge) {
                    return transitivity(ol, orr, right,
                                        std::move(op), std::move(bridge));
                }
            }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryStructuralDiff(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders, int line) {
        // Cheap structural peek (no WHNF): is the goal already a fully
        // applied `Equality.{u}(A, l, r)`? If not, decline immediately so we
        // pay nothing on non-equality / unreduced goals.
        auto* appR = std::get_if<Application>(&goalClosed->node);
        if (!appR) return nullptr;
        auto* appL = std::get_if<Application>(&appR->function->node);
        if (!appL) return nullptr;
        auto* appA = std::get_if<Application>(&appL->function->node);
        if (!appA) return nullptr;
        auto* head = std::get_if<Constant>(&appA->function->node);
        if (!head || head->name != "Equality"
            || head->universeArguments.size() != 1) return nullptr;
        // We assemble Equality.congruence / .transitivity proofs; bail if the
        // environment hasn't declared them yet (early bootstrap modules).
        if (environment_.lookup("Equality.congruence") == nullptr
            || environment_.lookup("Equality.transitivity") == nullptr) {
            return nullptr;
        }
        ExpressionPointer carrierType = appA->argument;
        ExpressionPointer left = appL->argument;
        ExpressionPointer right = appR->argument;
        LevelPointer carrierLevel = head->universeArguments[0];
        // A reflexive goal is the battery's job (a one-shot conversion);
        // we only handle genuinely differing sides.
        if (structurallyEqual(left, right)) return nullptr;
        return structuralDiffProve(localBinders, left, right,
                                    carrierType, carrierLevel, line);
    }

ExpressionPointer Elaborator::structuralDiffProve(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer left, ExpressionPointer right,
        ExpressionPointer carrierType, LevelPointer carrierLevel, int line) {
        autoProveSpend(1);
        // Discharge `left = right` as a unit from the LOCAL context. This is
        // the LEAF rule, reached only where the two sides cannot be
        // congruence-peeled (different head symbols, or not both
        // applications). It must stay cheap: an earlier version called
        // tryContextFactMatch here, which scans the whole library with a
        // WHNF-heavy fill — that made the pre-tactic cost MORE than the
        // battery it exists to pre-empt (it roughly doubled the heavy steps
        // in PAdic/absolute_value). tryLocalEqualityLeaf scans local binders
        // only, with a fuel-bounded defeq probe.
        auto contextLeaf = [&]() -> ExpressionPointer {
            return tryLocalEqualityLeaf(left, right, carrierType,
                                        carrierLevel, localBinders, line);
        };
        auto* leftApp = std::get_if<Application>(&left->node);
        auto* rightApp = std::get_if<Application>(&right->node);
        if (!leftApp || !rightApp) return contextLeaf();
        try {
            ExpressionPointer leftFn = leftApp->function;
            ExpressionPointer rightFn = rightApp->function;
            ExpressionPointer leftArg = leftApp->argument;
            ExpressionPointer rightArg = rightApp->argument;
            bool fnEq = structurallyEqual(leftFn, rightFn);
            bool argEq = structurallyEqual(leftArg, rightArg);
            if (fnEq && argEq) return nullptr;  // == left structurallyEqual right
            // Both sides differ AND have different head symbols → not a
            // congruence; treat the whole pair as one divergence leaf
            // (e.g. |nx| vs 1+kx, matched as a unit against the context).
            if (!fnEq && !argEq && spineHash(left) != spineHash(right)) {
                return contextLeaf();
            }

            auto closedType = [&](ExpressionPointer t) {
                return closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, t),
                    localBinders, localBinders.size());
            };
            ExpressionPointer argType = closedType(leftArg);
            LevelPointer argLevel = typeUniverseOf(localBinders, leftArg);
            ExpressionPointer fnType = closedType(leftFn);
            LevelPointer fnLevel = typeUniverseOf(localBinders, leftFn);
            ExpressionPointer appLeft = makeApplication(leftFn, leftArg);
            ExpressionPointer appType = closedType(appLeft);
            LevelPointer appLevel = typeUniverseOf(localBinders, appLeft);

            // congruence on the argument: leftFn leftArg = leftFn rightArg
            //   (motive λz. leftFn z), given a proof of leftArg = rightArg.
            auto argCongruence = [&](ExpressionPointer argProof) {
                ExpressionPointer motive = makeLambda("_sd_z", argType,
                    makeApplication(liftBoundVariables(leftFn, 1, 0),
                                    makeBoundVariable(0)));
                ExpressionPointer c = makeConstant(
                    "Equality.congruence", {argLevel, appLevel});
                c = makeApplication(std::move(c), argType);
                c = makeApplication(std::move(c), appType);
                c = makeApplication(std::move(c), std::move(motive));
                c = makeApplication(std::move(c), leftArg);
                c = makeApplication(std::move(c), rightArg);
                c = makeApplication(std::move(c), std::move(argProof));
                return c;
            };
            // congruence on the function: leftFn side = rightFn side
            //   (motive λf. f side), given a proof of leftFn = rightFn.
            auto fnCongruence = [&](ExpressionPointer side,
                                    ExpressionPointer fnProof) {
                ExpressionPointer motive = makeLambda("_sd_f", fnType,
                    makeApplication(makeBoundVariable(0),
                                    liftBoundVariables(side, 1, 0)));
                ExpressionPointer c = makeConstant(
                    "Equality.congruence", {fnLevel, appLevel});
                c = makeApplication(std::move(c), fnType);
                c = makeApplication(std::move(c), appType);
                c = makeApplication(std::move(c), std::move(motive));
                c = makeApplication(std::move(c), leftFn);
                c = makeApplication(std::move(c), rightFn);
                c = makeApplication(std::move(c), std::move(fnProof));
                return c;
            };

            if (argEq) {
                // only the function differs; the argument is shared.
                ExpressionPointer fnProof = structuralDiffProve(
                    localBinders, leftFn, rightFn, fnType, fnLevel, line);
                if (!fnProof) return nullptr;
                return fnCongruence(leftArg, std::move(fnProof));
            }
            if (fnEq) {
                // only the argument differs; the function is shared.
                ExpressionPointer argProof = structuralDiffProve(
                    localBinders, leftArg, rightArg, argType, argLevel, line);
                if (!argProof) return nullptr;
                return argCongruence(std::move(argProof));
            }
            // both differ: leftFn leftArg = leftFn rightArg = rightFn rightArg.
            ExpressionPointer argProof = structuralDiffProve(
                localBinders, leftArg, rightArg, argType, argLevel, line);
            if (!argProof) return nullptr;
            ExpressionPointer fnProof = structuralDiffProve(
                localBinders, leftFn, rightFn, fnType, fnLevel, line);
            if (!fnProof) return nullptr;
            ExpressionPointer cong1 = argCongruence(std::move(argProof));
            ExpressionPointer cong2 = fnCongruence(rightArg, std::move(fnProof));
            ExpressionPointer mid = makeApplication(leftFn, rightArg);
            ExpressionPointer appRight = makeApplication(rightFn, rightArg);
            ExpressionPointer trans = makeConstant(
                "Equality.transitivity", {appLevel});
            trans = makeApplication(std::move(trans), appType);
            trans = makeApplication(std::move(trans), appLeft);
            trans = makeApplication(std::move(trans), mid);
            trans = makeApplication(std::move(trans), appRight);
            trans = makeApplication(std::move(trans), std::move(cong1));
            trans = makeApplication(std::move(trans), std::move(cong2));
            return trans;
        } catch (const TypeError&) {
            return nullptr;
        } catch (const ElaborateError&) {
            return nullptr;
        }
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

        // Experimental: a cheap, purely-syntactic congruence diff that runs
        // BEFORE the defeq-heavy equality battery. When it applies it closes
        // the goal without unfolding any definition (the battery's diff walk
        // WHNFs at every level, which is what makes abs/quotient-arithmetic
        // steps cost hundreds of thousands of kernel steps). Off by default.
        if (structuralDiffEnabled_) {
            ExpressionPointer attempt = runTactic("structuralDiff",
                [&] { return tryStructuralDiff(
                    goalClosed, localBinders, line); });
            if (attempt) return attempt;
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
            ExpressionPointer attempt = runTactic("localFactExactMatch",
                [&] { return tryLocalFactExactMatch(
                    goalClosed, localBinders); });
            if (attempt) return attempt;
        }

        // B2 sign-judgment recursion — syntax-directed positivity: a
        // 0-anchored sign goal (`0 ≤ f(…)`, `0 < f(…)`, `f(…) ≠ 0`)
        // dispatches on its subject's head symbol to the (single)
        // registered rule and recurses on the subject's arguments.
        // Deterministic and linear in the subject term; placed after
        // the direct-hypothesis match (so stated facts still win) and
        // before the expensive context/library scans.
        {
            ExpressionPointer attempt = runTactic("signJudgmentRecursion",
                [&] { return trySignJudgmentRecursion(
                    goalClosed, localBinders, 12,
                    /*allowFormBridge=*/true); });
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
        // Quotient.equal_implies_equivalent, so proofs never name it. Placed before symmetryFlip
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
            + searchSuggestionsIfTopLevel(goalClosed, localBinders));
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
            long long t0 = monotonicNanos();
            ExpressionPointer result = nullptr;
            try {
                result = fn();
            } catch (const ElaborateError&) {
                result = nullptr;
            } catch (const TypeError&) {
                result = nullptr;
            }
            long long t1 = monotonicNanos();
            attempt.micros = (t1 - t0) / 1000;
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
        runProfiled("localFactExactMatch", [&] {
            return tryLocalFactExactMatch(goalClosed, localBinders);
        });
        runProfiled("signJudgmentRecursion", [&] {
            return trySignJudgmentRecursion(
                goalClosed, localBinders, 12,
                /*allowFormBridge=*/true);
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
            + searchSuggestionsIfTopLevel(goalClosed, localBinders));
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


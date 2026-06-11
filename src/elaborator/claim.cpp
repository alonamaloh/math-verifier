// Out-of-line Elaborator method definitions: claim-by-substitution and claim-by-cases
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::elaborateClaimBySubstitution(
        const SurfaceStructuredClaim& claim,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        Frame frame(*this,
            "claim by substitution at line "
            + std::to_string(line));
        // Build the candidate-equality list. Default: every equality
        // in scope (the existing bridge's pool). Narrowed: a single
        // equality the user supplied as `by substituting <eq>`.
        std::vector<ContextEquality> candidates;
        if (claim.byHint) {
            // Narrowed form. Elaborate <eq>; extract its components
            // as a single ContextEquality.
            ExpressionPointer eqProof = elaborateExpression(
                *claim.byHint, localBinders);
            // `by substituting (<equation>)`: the equation may be cited as a
            // bare proposition (e.g. `by substituting (a = b)`); auto-prove it
            // so the substitution runs against a proof of the equation.
            if (termIsProposition(localBinders, eqProof)) {
                eqProof = proveCitedFact(eqProof, localBinders, line);
            }
            ExpressionPointer eqProofTypeOpened;
            try {
                eqProofTypeOpened = inferTypeInLocalContext(
                    localBinders, eqProof);
            } catch (const TypeError&) {
                throwElaborate(
                    "`by substituting`: the supplied expression "
                    "doesn't typecheck as a proof");
            }
            EqualityComponents components;
            bool directEquality = true;
            try {
                components = extractEqualityComponents(
                    eqProofTypeOpened,
                    "by substituting argument", line);
            } catch (const ElaborateError&) {
                directEquality = false;
            }
            if (directEquality) {
                int N = static_cast<int>(localBinders.size());
                ContextEquality eq;
                eq.cost = 1;
                eq.source = "supplied via `by substituting`";
                eq.carrierType = closeOverLocalBinders(
                    components.carrierType, localBinders, N);
                eq.lhs = closeOverLocalBinders(
                    components.leftEndpoint, localBinders, N);
                eq.rhs = closeOverLocalBinders(
                    components.rightEndpoint, localBinders, N);
                eq.carrierLevel = components.carrierUniverseLevel;
                eq.proofExpr = eqProof;
                candidates.push_back(std::move(eq));
            } else {
                // A quantified equation (e.g. `by substituting
                // Natural.add_zero` with `add_zero : (a) → a + 0 = a`):
                // infer the arguments from the goal, mirroring what
                // `by <lemma>` and the unnamed `by substitution`
                // already do. Throws a tailored error when it can't.
                collectQuantifiedSubstitutionCandidates(
                    eqProof, eqProofTypeOpened, goalClosed,
                    localBinders, line, candidates);
            }
        } else {
            candidates = collectContextEqualities(
                goalClosed, localBinders, line);
            std::sort(candidates.begin(), candidates.end(),
                [](const ContextEquality& a, const ContextEquality& b) {
                    return a.cost < b.cost;
                });
        }
        // Goal candidates to search: first the closed form as the user
        // wrote it, then a deep-WHNF normalization (recursive WHNF
        // through Application spines). Under `unfold X in body`, the
        // surface goal type still mentions `X(args)`; only after
        // deep-WHNF does `X`'s body — and the equation's endpoint
        // buried inside it — become reachable for structural search.
        // We try the surface form first because it preserves the
        // user's intended motive shape; the deep form is the fallback
        // when the surface search comes up empty.
        std::vector<ExpressionPointer> goalForms;
        goalForms.push_back(goalClosed);
        ExpressionPointer goalDeepWhnf =
            deepWhnfThroughApplications(goalClosed);
        if (goalDeepWhnf.get() != goalClosed.get()) {
            goalForms.push_back(goalDeepWhnf);
        }
        // Third form: when the goal is headed by an opaque definition, the
        // substitution target may live inside its body. Force-unfold opaque
        // heads (search-only) so e.g. `divide_step(succ f, p, n) = …` exposes
        // its `cases monus(p, n) {…}` and the `monus(p, n)` endpoint becomes
        // reachable — replacing the old `unfold X in claim by substituting …`
        // wrap. Gated on an opaque head so ordinary goals skip the extra work;
        // the kernel's defeq bridge re-checks the rewritten goal.
        if (mentionsOpaqueDefinition(goalClosed)) {
            // Protect the substitution endpoints' own heads from being
            // force-unfolded — they are the targets we need to keep visible
            // (e.g. unfold `divide_step` to expose its `cases monus(p, n)`,
            // but keep `monus(p, n)` itself intact to match the `monus(p, n) =
            // 0` endpoint).
            std::set<std::string> protectedDefinitions;
            for (const ContextEquality& eq : candidates) {
                std::string l = headConstantName(eq.lhs);
                std::string r = headConstantName(eq.rhs);
                if (!l.empty()) protectedDefinitions.insert(l);
                if (!r.empty()) protectedDefinitions.insert(r);
            }
            ExpressionPointer goalForced =
                deepWhnfForcingOpaque(goalClosed, protectedDefinitions);
            if (goalForced.get() != goalClosed.get()
                && goalForced.get() != goalDeepWhnf.get()) {
                goalForms.push_back(goalForced);
            }
        }
        // For each candidate, both directions, try the bridge.
        // Track per-attempt outcomes so we can produce a useful
        // diagnostic when nothing closes — the user wants to know
        // whether the failure was "no occurrence of the endpoint" or
        // "occurrence found but rewritten goal not closeable."
        struct SubstAttempt {
            const char* direction;
            int surfaceOccurrences = 0;
            int deepWhnfOccurrences = 0;
            bool rewrittenProveFailed = false;
        };
        std::vector<SubstAttempt> attemptLog;
        for (const ContextEquality& eq : candidates) {
            for (int direction = 0; direction < 2; ++direction) {
                ExpressionPointer fromSide =
                    (direction == 0) ? eq.rhs : eq.lhs;
                ExpressionPointer toSide =
                    (direction == 0) ? eq.lhs : eq.rhs;
                // Find the goal form (surface, else deep-WHNF) in which
                // the endpoint occurs, and how many times.
                ExpressionPointer chosenForm;
                int occurrences = 0;
                int surfaceCount = 0;
                int deepCount = 0;
                for (size_t formIdx = 0;
                     formIdx < goalForms.size(); ++formIdx) {
                    int formOccurrences = 0;
                    abstractStructuralOccurrence(
                        goalForms[formIdx], fromSide,
                        /*currentDepth=*/0, formOccurrences);
                    if (formIdx == 0) {
                        surfaceCount = formOccurrences;
                    } else {
                        deepCount = formOccurrences;
                    }
                    if (formOccurrences > 0) {
                        chosenForm = goalForms[formIdx];
                        occurrences = formOccurrences;
                        break;
                    }
                }
                SubstAttempt attempt;
                attempt.direction = (direction == 0)
                    ? "rhs → lhs" : "lhs → rhs";
                attempt.surfaceOccurrences = surfaceCount;
                attempt.deepWhnfOccurrences = deepCount;
                if (occurrences == 0) {
                    attemptLog.push_back(attempt);
                    continue;
                }
                // Build the transport term from an abstracted motive body
                // (which occurrences are abstracted is the caller's choice)
                // and a proof of the rewritten goal. The motive shape is
                // the only thing that varies between a full and a masked
                // (single-occurrence) rewrite — the transport plumbing is
                // identical.
                auto buildTransport =
                    [&](ExpressionPointer abstractedBody,
                        ExpressionPointer proofRewritten) -> ExpressionPointer {
                    ExpressionPointer motive = makeLambda(
                        "_rewriteHole", eq.carrierType, abstractedBody);
                    ExpressionPointer eqForTransport;
                    ExpressionPointer transportLhs;
                    ExpressionPointer transportRhs;
                    if (direction == 0) {
                        eqForTransport = eq.proofExpr;
                        transportLhs = eq.lhs;
                        transportRhs = eq.rhs;
                    } else {
                        eqForTransport = makeConstant(
                            "Equality.symmetry", {eq.carrierLevel});
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
                };
                auto tryCloseAndBuild =
                    [&](ExpressionPointer abstractedBody,
                        int budget) -> ExpressionPointer {
                    ExpressionPointer rewrittenGoal = substitute(
                        abstractedBody, 0, toSide);
                    try {
                        ExpressionPointer proofRewritten = autoProveClaim(
                            rewrittenGoal, localBinders, line, budget);
                        return buildTransport(abstractedBody, proofRewritten);
                    } catch (const ElaborateError&) {
                        return nullptr;
                    } catch (const TypeError&) {
                        return nullptr;
                    }
                };
                // Phase 1: try rewriting each SUBSET of the occurrences and
                // closing CHEAPLY (transportBudget 0 — a hypothesis/fact
                // match, no further equality-bridge search). This finds the
                // intended rewrite when the endpoint occurs several times —
                // e.g. only the standalone `0` in `successor(0) ≤ 0`, which
                // lands on a hypothesis — and returns fast, instead of
                // rewriting ALL occurrences into an unprovable goal and then
                // burning the full search on it. Bounded to a small
                // occurrence count so the 2^n subset sweep stays cheap.
                constexpr int maxOccurrencesForSubsetSearch = 6;
                if (occurrences <= maxOccurrencesForSubsetSearch) {
                    for (uint32_t mask = 1;
                         mask < (1u << occurrences); ++mask) {
                        int counter = 0;
                        ExpressionPointer maskedBody =
                            abstractStructuralOccurrenceMasked(
                                chosenForm, fromSide, /*currentDepth=*/0,
                                counter, mask);
                        ExpressionPointer result =
                            tryCloseAndBuild(maskedBody, /*budget=*/0);
                        if (result) return result;
                    }
                }
                // Phase 2: rewrite ALL occurrences and close with the full
                // auto-prover (default budget — may recurse through one
                // equality bridge, which some goals legitimately need).
                {
                    int counter = 0;
                    ExpressionPointer allBody = abstractStructuralOccurrence(
                        chosenForm, fromSide, /*currentDepth=*/0, counter);
                    ExpressionPointer result =
                        tryCloseAndBuild(allBody, /*budget=*/1);
                    if (result) return result;
                }
                attempt.rewrittenProveFailed = true;
                attemptLog.push_back(attempt);
                continue;
            }
        }
        // Hypothesis-rewriting fallback (narrowed `by substituting <eq>`
        // only). Goal-rewriting can't reach an endpoint hidden behind a
        // FOLDED definition — e.g. Real `x ≤ y` := `IsNonneg(y - x)`, so
        // the goal `x+z ≤ y+z` never shows `(y+z)-(x+z)` without unfolding.
        // The dual of the explicit `rewrite(eq, hyp)` works: rewrite an
        // in-scope HYPOTHESIS by the equation and keep it if the result is
        // def-equal to the goal (def-eq unfolds the definition). Bounded to
        // the one supplied equality × 2 directions × in-scope proofs; only
        // runs once goal-rewriting has already failed.
        if (claim.byHint && !candidates.empty()) {
            int N = static_cast<int>(localBinders.size());
            Context context = buildContextFromLocalBinders(localBinders);
            ExpressionPointer goalOpened = openOverLocalBinders(
                goalClosed, localBinders, N);
            const ContextEquality& eq = candidates.front();
            for (int dir = 0; dir < 2; ++dir) {
                ExpressionPointer fromSide = (dir == 0) ? eq.lhs : eq.rhs;
                ExpressionPointer toSide = (dir == 0) ? eq.rhs : eq.lhs;
                // eqForTransport : fromSide = toSide.
                ExpressionPointer eqForTransport;
                if (dir == 0) {
                    eqForTransport = eq.proofExpr;
                } else {
                    eqForTransport = makeConstant(
                        "Equality.symmetry", {eq.carrierLevel});
                    for (ExpressionPointer a :
                         {eq.carrierType, eq.lhs, eq.rhs, eq.proofExpr}) {
                        eqForTransport = makeApplication(eqForTransport, a);
                    }
                }
                for (int b = N - 1; b >= 0; --b) {
                    ExpressionPointer hyp = makeBoundVariable(N - 1 - b);
                    ExpressionPointer hypTypeOpened;
                    try {
                        hypTypeOpened = inferTypeInLocalContext(
                            localBinders, hyp);
                    } catch (...) { continue; }
                    bool isProp = false;
                    try {
                        isProp = typeIsProposition(context,
                            weakHeadNormalForm(environment_, hypTypeOpened));
                    } catch (...) { isProp = false; }
                    if (!isProp) continue;
                    ExpressionPointer hypType = closeOverLocalBinders(
                        hypTypeOpened, localBinders, N);
                    // Abstract `fromSide` in the hypothesis type — the
                    // unreduced form first (preserves the user-visible
                    // shape), then WHNF (peels a folded def like
                    // `LessOrEqual` to expose `y - x`). Mirrors the
                    // explicit `rewrite(eq, term)` search.
                    ExpressionPointer chosen;
                    int counter = 0;
                    abstractStructuralOccurrence(hypType, fromSide, 0,
                                                  counter);
                    if (counter > 0) {
                        chosen = hypType;
                    } else {
                        ExpressionPointer whnf = closeOverLocalBinders(
                            weakHeadNormalForm(environment_, hypTypeOpened),
                            localBinders, N);
                        int whnfCount = 0;
                        abstractStructuralOccurrence(whnf, fromSide, 0,
                                                      whnfCount);
                        if (whnfCount == 0) continue;
                        chosen = whnf;
                    }
                    int abstractionCounter = 0;
                    ExpressionPointer body = abstractStructuralOccurrence(
                        chosen, fromSide, 0, abstractionCounter);
                    ExpressionPointer motive = makeLambda(
                        "_rewriteHole", eq.carrierType, body);
                    ExpressionPointer transport = makeConstant(
                        "Equality.transport_proposition", {eq.carrierLevel});
                    for (ExpressionPointer a : {eq.carrierType, motive,
                             fromSide, toSide, eqForTransport, hyp}) {
                        transport = makeApplication(transport, a);
                    }
                    ExpressionPointer transportTypeOpened;
                    try {
                        transportTypeOpened = inferTypeInLocalContext(
                            localBinders, transport);
                    } catch (...) { continue; }
                    bool matchesGoal = false;
                    try {
                        matchesGoal = isDefinitionallyEqual(environment_,
                            context, transportTypeOpened, goalOpened);
                    } catch (...) { matchesGoal = false; }
                    if (matchesGoal) return transport;
                }
            }
        }
        if (claim.byHint) {
            // For the named form there's a single equality — break down
            // the per-direction outcomes so the user can distinguish
            // "endpoint not present" from "endpoint present but
            // rewritten goal isn't proveable."
            std::string detail;
            for (const SubstAttempt& a : attemptLog) {
                detail += "\n      ";
                detail += a.direction;
                detail += ": ";
                if (a.surfaceOccurrences == 0
                    && a.deepWhnfOccurrences == 0) {
                    detail +=
                        "0 occurrences (surface or deep-WHNF)";
                } else {
                    detail += "found " +
                        std::to_string(std::max(a.surfaceOccurrences,
                                                  a.deepWhnfOccurrences))
                        + " occurrence(s)";
                    if (a.surfaceOccurrences == 0
                        && a.deepWhnfOccurrences > 0) {
                        detail +=
                            " — only after deep-WHNF reduction";
                    }
                    if (a.rewrittenProveFailed) {
                        detail += "; rewritten goal not closeable by "
                                  "the auto-prover";
                    }
                }
            }
            throwElaborate(
                "`by substituting <eq>` couldn't close the goal."
                "\n  Direction search:" + detail
                + "\n  (If a direction shows occurrences but the "
                  "rewritten goal failed, the rewrite happened — but "
                  "the auto-prover couldn't discharge the result. "
                  "Add `by <proof>` to close it manually.)");
        }
        throwElaborate(
            "`by substitution` couldn't close the goal: no in-scope "
            "equality lets the auto-prover reach a provable form "
            "(consider `by substituting <specific eq>` to narrow, "
            "or supply an explicit `by <proof>`)");
    }

void Elaborator::collectQuantifiedSubstitutionCandidates(
        ExpressionPointer citedProof,
        ExpressionPointer citedTypeOpened,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line,
        std::vector<ContextEquality>& out) {
        int N = static_cast<int>(localBinders.size());
        std::string citedPrinted = prettyPrintInLocalScope(
            citedProof, localBinders);
        // Peel the Pi chain off the citation's type (closed over the
        // local binders, so the chain's own BoundVariables are the only
        // ones below `binderCount` — the metavariable slots
        // matchAgainstPattern expects).
        ExpressionPointer citedTypeClosed = closeOverLocalBinders(
            citedTypeOpened, localBinders, N);
        ExpressionPointer conclusion = citedTypeClosed;
        int binderCount = 0;
        while (auto* pi = std::get_if<Pi>(&conclusion->node)) {
            conclusion = pi->codomain;
            ++binderCount;
        }
        // The conclusion must be `Equality(carrier, lhs, rhs)`.
        auto* eqApp3 = std::get_if<Application>(&conclusion->node);
        auto* eqApp2 = eqApp3
            ? std::get_if<Application>(&eqApp3->function->node) : nullptr;
        auto* eqApp1 = eqApp2
            ? std::get_if<Application>(&eqApp2->function->node) : nullptr;
        auto* eqHead = eqApp1
            ? std::get_if<Constant>(&eqApp1->function->node) : nullptr;
        if (binderCount == 0 || !eqHead || eqHead->name != "Equality") {
            throwElaborate(
                "`by substituting`: the supplied expression's "
                "type is not an equality `a = b`"
                + std::string(binderCount > 0
                    ? " — '" + citedPrinted + "' is a function whose "
                      "conclusion is not an equality"
                    : ""));
        }
        ExpressionPointer lhsPattern = eqApp2->argument;
        ExpressionPointer rhsPattern = eqApp3->argument;
        // Scan the goal's Application subterms (surface form first,
        // then the deep-WHNF fallback the bridge itself uses) for an
        // instance of either endpoint pattern; each complete match
        // instantiates the citation into a concrete equality candidate.
        // Bare-BoundVariable patterns are skipped — they match every
        // subterm and carry no inference signal.
        std::vector<ContextEquality> inferred;
        std::function<void(ExpressionPointer)> scan =
            [&](ExpressionPointer subexpr) {
            auto* app = std::get_if<Application>(&subexpr->node);
            if (!app) return;
            for (const ExpressionPointer& pattern :
                     {lhsPattern, rhsPattern}) {
                if (std::holds_alternative<BoundVariable>(pattern->node)) {
                    continue;
                }
                std::vector<ExpressionPointer> bindings(binderCount);
                if (!matchAgainstPattern(pattern, subexpr,
                                           binderCount, bindings)) {
                    continue;
                }
                bool allBound = true;
                for (const auto& binding : bindings) {
                    if (!binding) { allBound = false; break; }
                }
                if (!allBound) continue;
                // Assemble `cited(binding_for_BV(n-1), …, BV(0))` —
                // outermost binder first, matching the Pi chain.
                ExpressionPointer instance = citedProof;
                for (int i = binderCount - 1; i >= 0; --i) {
                    instance = makeApplication(instance, bindings[i]);
                }
                ExpressionPointer instanceTypeOpened;
                try {
                    instanceTypeOpened = inferTypeInLocalContext(
                        localBinders, instance);
                } catch (const TypeError&) { continue; }
                  catch (const ElaborateError&) { continue; }
                EqualityComponents components;
                try {
                    components = extractEqualityComponents(
                        instanceTypeOpened,
                        "by substituting argument", line);
                } catch (const ElaborateError&) { continue; }
                ContextEquality eq;
                eq.cost = 1;
                eq.source = "supplied via `by substituting` ("
                    + citedPrinted + ", arguments inferred)";
                eq.carrierType = closeOverLocalBinders(
                    components.carrierType, localBinders, N);
                eq.lhs = closeOverLocalBinders(
                    components.leftEndpoint, localBinders, N);
                eq.rhs = closeOverLocalBinders(
                    components.rightEndpoint, localBinders, N);
                eq.carrierLevel = components.carrierUniverseLevel;
                eq.proofExpr = std::move(instance);
                bool duplicate = false;
                for (const ContextEquality& seen : inferred) {
                    if (structurallyEqual(seen.lhs, eq.lhs)
                        && structurallyEqual(seen.rhs, eq.rhs)) {
                        duplicate = true;
                        break;
                    }
                }
                if (!duplicate) inferred.push_back(std::move(eq));
            }
            scan(app->function);
            scan(app->argument);
        };
        scan(goalClosed);
        ExpressionPointer goalDeepWhnf =
            deepWhnfThroughApplications(goalClosed);
        if (goalDeepWhnf.get() != goalClosed.get()) {
            scan(goalDeepWhnf);
        }
        if (inferred.empty()) {
            throwElaborate(
                "`by substituting`: '" + citedPrinted
                + "' is a quantified equation — it still expects "
                + std::to_string(binderCount)
                + " argument(s), and no instance of its left- or "
                  "right-hand side occurs in the goal, so they could "
                  "not be inferred. Apply it explicitly (`by "
                  "substituting " + citedPrinted + "(…)`), or use the "
                  "unnamed `by substitution` to search every equality "
                  "in scope.");
        }
        for (ContextEquality& eq : inferred) {
            out.push_back(std::move(eq));
        }
    }

ExpressionPointer Elaborator::elaborateClaimByCases(
        const SurfaceStructuredClaim& claim,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {
        Frame frame(*this,
            "claim by cases at line " + std::to_string(line));

        if (claim.arms.size() < 2) {
            throwElaborate(
                "`by cases` needs at least 2 arms; got "
                + std::to_string(claim.arms.size()));
        }
        const size_t armCount = claim.arms.size();

        // The goal each arm must prove. A `goal` proposition (`claim goal
        // by cases …`, and the `done`/`okay` desugaring) is the expected
        // type itself.
        ExpressionPointer goalClosed;
        bool propositionIsGoal = claim.proposition
            && std::holds_alternative<SurfaceGoal>(claim.proposition->node);
        if (claim.proposition && !propositionIsGoal) {
            goalClosed = elaborateExpression(
                *claim.proposition, localBinders);
        } else if (expectedType) {
            goalClosed = expectedType;
        } else {
            throwElaborate(
                "`claim by cases` / `done by cases` needs either a "
                "proposition or an expected type from context");
        }

        // Elaborate each arm's disjunct proposition.
        std::vector<ExpressionPointer> disjuncts;
        for (const auto& arm : claim.arms) {
            disjuncts.push_back(
                elaborateExpression(*arm.disjunctType, localBinders));
        }
        // Right-nested disjunction `Or` (a non-polymorphic Proposition):
        // restDisjunction[i] = Pᵢ ∨ Pᵢ₊₁ ∨ … ∨ Pₙ₋₁, so restDisjunction[0]
        // is the whole `P₀ ∨ … ∨ Pₙ₋₁` the cases must cover.
        auto makeOr = [&](ExpressionPointer a, ExpressionPointer b) {
            return makeApplication(
                makeApplication(makeConstant("Or", {}), a), b);
        };
        std::vector<ExpressionPointer> restDisjunction(armCount);
        restDisjunction[armCount - 1] = disjuncts[armCount - 1];
        for (int i = static_cast<int>(armCount) - 2; i >= 0; --i) {
            restDisjunction[i] = makeOr(disjuncts[i], restDisjunction[i + 1]);
        }
        ExpressionPointer expectedDisjunction = restDisjunction[0];

        // Find OR synthesize the disjunction via the unified hammer
        // dispatch. This is the same "find or synthesize" function
        // bare `claim P;` uses — local hypothesis match, library
        // scan, transitivity, the lot. If nothing in scope proves
        // the disjunction, the dispatch error message (wrapped by
        // the Frame above) tells the user exactly what failed.
        ExpressionPointer disjProof;
        try {
            disjProof = autoProveClaim(
                expectedDisjunction, localBinders, line);
        } catch (const ElaborateError&) {
            throwElaborate(
                "couldn't automatically prove `"
                + prettyPrintInLocalScope(
                      expectedDisjunction, localBinders)
                + "` to finish off `by cases` — either bring that "
                "disjunction into scope explicitly (`claim <P₀> ∨ … ∨ <Pₙ₋₁> "
                "by …;`), or check that the cases really do cover the goal");
        }

        // Build each arm's lambda. Body is elaborated under
        // localBinders + the disjunct hypothesis. The hypothesis
        // takes the user-supplied `as name` if present, else
        // `_disjunct_hypothesis` (reachable via `given (P)` /
        // library lookup). The goal is lifted by 1 to account for
        // the extra binder.
        ExpressionPointer goalLifted =
            liftBoundVariables(goalClosed, 1, 0);
        auto buildArmLambda =
            [&](size_t index, ExpressionPointer domain)
                -> ExpressionPointer {
            const SurfaceStructuredClaimArm& arm = claim.arms[index];
            std::string binderName = arm.binderName.empty()
                ? "_disjunct_hypothesis" : arm.binderName;
            std::vector<LocalBinder> extendedBinders = localBinders;
            extendedBinders.push_back({binderName, domain});
            // Frame anchors any error in this arm at the arm's own position,
            // not at the enclosing eliminator (the misleading "case for
            // 'Exists.introduce'" / wrong-line report otherwise).
            Frame armFrame(*this,
                "`by cases` arm at line " + std::to_string(arm.line),
                extendedBinders, goalLifted, arm.line, arm.column);
            ExpressionPointer body = elaborateExpression(
                *arm.body, extendedBinders, goalLifted);
            // Coerce the arm body to the goal, exactly as a lambda body or a
            // `cases` arm is coerced. This lets an arm state a proof of one
            // DISJUNCT (`calc n = … = 0`) and have the disjunction-injection
            // coercion wrap the matching `Or.introduce*` — consistent with
            // `cases` arms, instead of demanding an explicit `Or.introduceLeft`.
            body = coerceToExpectedTypeViaDiff(
                extendedBinders, body, goalLifted);
            // If the (coerced) body still doesn't prove the goal, report it
            // here, at the arm, with a math-shaped message — rather than
            // letting the mismatch surface later as a kernel Pi-domain error
            // pinned to the surrounding `obtain`/eliminator.
            try {
                ExpressionPointer bodyTypeOpened =
                    inferTypeInLocalContext(extendedBinders, body);
                ExpressionPointer goalOpened = openOverLocalBinders(
                    goalLifted, extendedBinders, extendedBinders.size());
                if (!isDefinitionallyEqual(
                        environment_,
                        buildContextFromLocalBinders(extendedBinders),
                        bodyTypeOpened, goalOpened)) {
                    ExpressionPointer bodyTypeClosed = closeOverLocalBinders(
                        bodyTypeOpened, extendedBinders, extendedBinders.size());
                    throwElaborate(
                        "this `by cases` arm must prove the goal\n      "
                        + prettyPrintInLocalScope(goalLifted, extendedBinders)
                        + "\n  but its body proves\n      "
                        + prettyPrintInLocalScope(bodyTypeClosed, extendedBinders)
                        + "\n  — if that is meant to be one side of the "
                        "disjunction, make sure it matches a disjunct exactly "
                        "(it is then wrapped automatically); otherwise this "
                        "case does not close the goal");
                }
            } catch (const TypeError&) {
                // Body isn't well-typed on its own — let the normal flow
                // surface that error.
            }
            warnIfBinderUnused(
                arm.binderName, body, arm.line, arm.column,
                "`case ... as`");
            return makeLambda(binderName, domain, body);
        };
        // Fold the arms into nested `Or.eliminate` calls. Define
        //   eliminator(i) : (Pᵢ ∨ … ∨ Pₙ₋₁) → Goal
        //     eliminator(n-1) = armLambda(n-1)
        //     eliminator(i)   = λ (tail : Pᵢ ∨ rest).
        //                         Or.eliminate(Pᵢ, rest, Goal,
        //                                      armLambda(i), eliminator(i+1),
        //                                      tail)
        // The top-level call feeds the proved disjunction directly. For two
        // arms this is exactly `Or.eliminate(P₀, P₁, Goal, arm₀, arm₁, proof)`.
        std::function<ExpressionPointer(size_t)> eliminator =
            [&](size_t i) -> ExpressionPointer {
                if (i + 1 == armCount) {
                    return buildArmLambda(i, disjuncts[i]);
                }
                ExpressionPointer armLambda = buildArmLambda(i, disjuncts[i]);
                ExpressionPointer restEliminator = eliminator(i + 1);
                // Inside the new `tail` binder (de Bruijn 0), the closed
                // sub-terms shift up by one.
                auto lift = [](const ExpressionPointer& e) {
                    return liftBoundVariables(e, 1, 0);
                };
                ExpressionPointer body = makeConstant("Or.eliminate", {});
                body = makeApplication(body, lift(disjuncts[i]));
                body = makeApplication(body, lift(restDisjunction[i + 1]));
                body = makeApplication(body, lift(goalClosed));
                body = makeApplication(body, lift(armLambda));
                body = makeApplication(body, lift(restEliminator));
                body = makeApplication(body, makeBoundVariable(0));
                return makeLambda(
                    "_disjunction_tail", restDisjunction[i], body);
            };
        ExpressionPointer call = makeConstant("Or.eliminate", {});
        call = makeApplication(call, disjuncts[0]);
        call = makeApplication(call, restDisjunction[1]);
        call = makeApplication(call, goalClosed);
        call = makeApplication(call, buildArmLambda(0, disjuncts[0]));
        call = makeApplication(call, eliminator(1));
        call = makeApplication(call, disjProof);
        return call;
    }


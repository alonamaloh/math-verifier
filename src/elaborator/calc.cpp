// Out-of-line Elaborator method definitions: the calc tactic (calc / calc-over-preorder + per-step diff proving)
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::elaborateCalcPreorder(
        const SurfaceCalc& calc,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "calc block at line " + std::to_string(line),
            localBinders, expectedType, line, column);
        ExpressionPointer e0 = elaborateExpression(
            *calc.initialExpression, localBinders);
        ExpressionPointer carrierTypeOpen =
            inferTypeInLocalContext(localBinders, e0);
        ExpressionPointer carrierType = closeOverLocalBinders(
            carrierTypeOpen, localBinders, localBinders.size());
        LevelPointer carrierLevel = typeUniverseOf(localBinders, e0);
        auto* carrierConstant =
            std::get_if<Constant>(&carrierTypeOpen->node);
        std::string carrierTypeName =
            carrierConstant ? carrierConstant->name : std::string{};

        // The single relation symbol used by all non-`=` steps.
        std::string symbol;
        for (const auto& s : calc.steps) {
            if (s.relationOperator.empty()) continue;
            if (symbol.empty()) symbol = s.relationOperator;
            else if (symbol != s.relationOperator) {
                throwElaborate(
                    "calc chain mixes the relations '" + symbol + "' and '"
                    + s.relationOperator + "'; a single calc may use only "
                    "one non-`=` relation");
            }
        }
        // Resolve the relation function (operator registry, then the
        // built-in Natural fallback for `∣`).
        std::string relationFn = environment_.lookupOperator(
            symbol, carrierTypeName, carrierTypeName);
        if (relationFn.empty() && carrierTypeName == "Natural"
            && symbol == "∣") {
            relationFn = "Natural.divides";
        }
        if (relationFn.empty()) {
            throwElaborate(
                "calc step uses '" + symbol + "' but no such relation is "
                "available on " + carrierTypeName + " — register one via "
                "`operator (" + symbol + ") on (" + carrierTypeName + ", "
                + carrierTypeName + ") := <fn>;`");
        }
        // Transitivity lemma: accept either the dotted `<R>.transitive`
        // convention (the order relations) or the `<R>_transitive`
        // convention (e.g. Natural.divides_transitive).
        std::string transitiveName;
        for (const std::string& candidate :
             {relationFn + ".transitive", relationFn + "_transitive"}) {
            if (environment_.lookup(candidate)) {
                transitiveName = candidate;
                break;
            }
        }
        if (transitiveName.empty()) {
            throwElaborate(
                "calc over '" + symbol + "' needs a transitivity lemma "
                + relationFn + ".transitive (or " + relationFn
                + "_transitive) in scope");
        }
        // R(x, y) as a Proposition.
        auto relationType =
            [&](ExpressionPointer x, ExpressionPointer y) {
                return makeApplication(
                    makeApplication(makeConstant(relationFn), x), y);
            };
        // Equality(carrier, x, y).
        auto equalityType =
            [&](ExpressionPointer x, ExpressionPointer y) {
                return makeApplication(makeApplication(makeApplication(
                    makeConstant("Equality", {carrierLevel}),
                    carrierType), x), y);
            };

        // Elaborate every endpoint and its step proof.
        std::vector<ExpressionPointer> endpoints;
        endpoints.push_back(e0);
        std::vector<ExpressionPointer> proofs;
        std::vector<bool> isEquality;
        ExpressionPointer previous = e0;
        Context context = buildContextFromLocalBinders(localBinders);
        for (size_t k = 0; k < calc.steps.size(); ++k) {
            const auto& step = calc.steps[k];
            ExpressionPointer next = elaborateExpression(
                *step.nextExpression, localBinders, carrierType);
            bool eqStep = step.relationOperator.empty();
            ExpressionPointer wantType = eqStep
                ? equalityType(previous, next)
                : relationType(previous, next);
            ExpressionPointer proof;
            if (step.stepProof) {
                proof = elaborateExpression(
                    *step.stepProof, localBinders, wantType);
            } else {
                proof = autoProveClaim(wantType, localBinders, step.line);
            }
            // Confirm the proof has the claimed step type.
            ExpressionPointer proofType =
                inferTypeInLocalContext(localBinders, proof);
            ExpressionPointer wantOpened = openOverLocalBinders(
                wantType, localBinders, localBinders.size());
            if (!isDefinitionallyEqual(environment_, context,
                                        proofType, wantOpened)) {
                throwElaborate(
                    "calc step " + std::to_string(k + 1)
                    + " proof does not have the claimed type `"
                    + prettyPrintInLocalScope(wantType, localBinders) + "`");
            }
            endpoints.push_back(next);
            proofs.push_back(proof);
            isEquality.push_back(eqStep);
            previous = next;
        }

        // Index of the first `∣`/`⊆` step (guaranteed to exist — the
        // dispatch only routes here when one is present).
        size_t firstRel = 0;
        while (firstRel < isEquality.size() && isEquality[firstRel]) {
            ++firstRel;
        }

        // Phase A: fold the leading `=` prefix endpoints[0..firstRel] into
        // a single `endpoints[0] = endpoints[firstRel]`.
        ExpressionPointer prefixEquality;  // null when firstRel == 0
        if (firstRel > 0) {
            prefixEquality = proofs[0];
            for (size_t k = 1; k < firstRel; ++k) {
                ExpressionPointer call =
                    makeConstant("Equality.transitivity", {carrierLevel});
                for (ExpressionPointer a : {carrierType, endpoints[0],
                                             endpoints[k], endpoints[k + 1],
                                             prefixEquality, proofs[k]}) {
                    call = makeApplication(call, a);
                }
                prefixEquality = call;
            }
        }

        // Phase B: from the first `∣` step, fold the rest. `current`
        // always proves `R(endpoints[firstRel], curRight)`; `=` steps
        // transport its right endpoint, `∣` steps compose by transitivity.
        ExpressionPointer left = endpoints[firstRel];
        ExpressionPointer current = proofs[firstRel];
        for (size_t k = firstRel + 1; k < proofs.size(); ++k) {
            ExpressionPointer mid = endpoints[k];
            ExpressionPointer next = endpoints[k + 1];
            if (isEquality[k]) {
                // transport_proposition(λz. R(left, z), mid, next, proof,
                //                        current) : R(left, next)
                ExpressionPointer predicate = makeLambda(
                    "z", carrierType,
                    makeApplication(
                        makeApplication(makeConstant(relationFn),
                            shift(left, 1)),
                        makeBoundVariable(0)));
                ExpressionPointer call = makeConstant(
                    "Equality.transport_proposition", {carrierLevel});
                for (ExpressionPointer a : {carrierType, predicate, mid,
                                             next, proofs[k], current}) {
                    call = makeApplication(call, a);
                }
                current = call;
            } else {
                ExpressionPointer call = makeConstant(transitiveName);
                for (ExpressionPointer a : {left, mid, next,
                                             current, proofs[k]}) {
                    call = makeApplication(call, a);
                }
                current = call;
            }
        }

        // Phase C: fold the prefix equality `endpoints[0] = left` into the
        // left endpoint: R(endpoints[0], last) from R(left, last).
        if (prefixEquality) {
            ExpressionPointer last = endpoints.back();
            // symmetry : left = endpoints[0]
            ExpressionPointer symmetry = makeConstant(
                "Equality.symmetry", {carrierLevel});
            for (ExpressionPointer a : {carrierType, endpoints[0], left,
                                         prefixEquality}) {
                symmetry = makeApplication(symmetry, a);
            }
            // transport_proposition(λz. R(z, last), left, endpoints[0],
            //                        symmetry, current) : R(endpoints[0], last)
            ExpressionPointer predicate = makeLambda(
                "z", carrierType,
                makeApplication(
                    makeApplication(makeConstant(relationFn),
                        makeBoundVariable(0)),
                    shift(last, 1)));
            ExpressionPointer call = makeConstant(
                "Equality.transport_proposition", {carrierLevel});
            for (ExpressionPointer a : {carrierType, predicate, left,
                                         endpoints[0], symmetry, current}) {
                call = makeApplication(call, a);
            }
            current = call;
        }

        // Final sanity check against the intended conclusion.
        ExpressionPointer resultType = relationType(
            endpoints[0], endpoints.back());
        ExpressionPointer resultTypeOpened = openOverLocalBinders(
            resultType, localBinders, localBinders.size());
        ExpressionPointer currentType =
            inferTypeInLocalContext(localBinders, current);
        if (!isDefinitionallyEqual(environment_, context,
                                    currentType, resultTypeOpened)) {
            throwElaborate(
                "calc chain over '" + symbol + "' did not fold to `"
                + prettyPrintInLocalScope(resultType, localBinders)
                + "` (the transitivity lemma " + transitiveName
                + " may take its arguments in a different order)");
        }
        return current;
    }

ExpressionPointer Elaborator::elaborateCalc(
        const SurfaceCalc& calc,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        // Generic-preorder calc (`∣`, `⊆`, …): any step carrying a
        // relation-operator symbol routes the whole chain to the preorder
        // fold, which uses the carrier's registered relation + its
        // transitivity lemma and absorbs interleaved `=` steps by
        // transport. The built-in order engine below handles =/≤/</≥/>.
        for (const auto& s : calc.steps) {
            if (!s.relationOperator.empty()) {
                return elaborateCalcPreorder(
                    calc, localBinders, expectedType, line, column);
            }
        }
        Frame frame(*this,
            "calc block at line " + std::to_string(line),
            localBinders, expectedType, line, column);
        ExpressionPointer previousKernel = elaborateExpression(
            *calc.initialExpression, localBinders);
        ExpressionPointer carrierTypeOpen =
            inferTypeInLocalContext(localBinders, previousKernel);
        ExpressionPointer carrierType = closeOverLocalBinders(
            carrierTypeOpen, localBinders, localBinders.size());
        LevelPointer carrierLevel =
            typeUniverseOf(localBinders, previousKernel);

        // Resolve the carrier's <T>.LessOrEqual and <T>.LessThan
        // relations (and their reflexive / transitive / weaken lemmas)
        // lazily, on first use. The operator registry — populated by
        // `operator (≤) on (T, T) := <T>.LessOrEqual;` and the parallel
        // `<`/`>`/`≥` registrations — drives the name lookup. Natural
        // has no namespaced wrapper around its inductive `LessOrEqual`,
        // so we fall back to bare `LessOrEqual` for it (and don't
        // support `<` on Natural in calc, since there's no Natural-side
        // LessThan type with transitive_left/right lemmas).
        auto* carrierConstant =
            std::get_if<Constant>(&carrierTypeOpen->node);
        std::string carrierTypeName =
            carrierConstant ? carrierConstant->name : std::string{};
        std::string leqRelationName;       // e.g. "Real.LessOrEqual"
        std::string leqReflexiveName;      // e.g. "Real.LessOrEqual.reflexive"
        std::string leqTransitiveName;     // e.g. "Real.LessOrEqual.transitive"
        bool transitiveTakesProofsSwapped = false;
        std::string ltRelationName;            // e.g. "Real.LessThan"
        std::string ltTransitiveLeftName;      // e.g. "Real.LessThan.transitive_left"
        std::string ltTransitiveRightName;     // e.g. "Real.LessThan.transitive_right"
        std::string ltWeakenName;              // e.g. "Real.LessThan.weaken"
        auto resolveLeqNames = [&]() {
            if (!leqRelationName.empty()) return;
            std::string registered = environment_.lookupOperator(
                "≤", carrierTypeName, carrierTypeName);
            if (!registered.empty()) {
                leqRelationName = registered;
                leqReflexiveName = registered + ".reflexive";
                leqTransitiveName = registered + ".transitive";
            } else if (carrierTypeName == "Natural") {
                // Natural's ≤ falls back to the bare inductive
                // `LessOrEqual`. Its transitive lemma takes the proofs
                // in (b≤c, a≤b) order — historical accident from the
                // pattern-match-on-second-proof construction — so flag
                // the swap for the composition step below.
                leqRelationName = "LessOrEqual";
                leqReflexiveName = "LessOrEqual.reflexivity";
                leqTransitiveName = "LessOrEqual.transitive";
                transitiveTakesProofsSwapped = true;
            } else {
                throwElaborate(
                    "calc step uses '≤'/'≥' but no operator '≤' is "
                    "registered on (" + carrierTypeName + ", "
                    + carrierTypeName + ") — register one via "
                    "`operator (≤) on (" + carrierTypeName + ", "
                    + carrierTypeName + ") := <fn>;` first");
            }
        };
        auto resolveLtNames = [&]() {
            if (!ltRelationName.empty()) return;
            std::string registered = environment_.lookupOperator(
                "<", carrierTypeName, carrierTypeName);
            if (registered.empty()) {
                throwElaborate(
                    "calc step uses '<'/'>' but no operator '<' is "
                    "registered on (" + carrierTypeName + ", "
                    + carrierTypeName + ") — register one via "
                    "`operator (<) on (" + carrierTypeName + ", "
                    + carrierTypeName + ") := <fn>;` first");
            }
            ltRelationName = registered;
            ltTransitiveLeftName = registered + ".transitive_left";
            ltTransitiveRightName = registered + ".transitive_right";
            ltWeakenName = registered + ".weaken";
        };

        // Classify a CalcRelation along two axes:
        //   - direction: Forward (<, ≤), Backward (>, ≥), or Neutral (=).
        //     A chain may not mix Forward with Backward steps.
        //   - strictness: Equality, Weak (≤/≥), or Strict (<, >).
        enum class Direction { Neutral, Forward, Backward };
        enum class Strictness { Equality, Weak, Strict };
        auto directionOf = [](CalcRelation r) -> Direction {
            switch (r) {
                case CalcRelation::LessOrEqual:
                case CalcRelation::LessThan:
                    return Direction::Forward;
                case CalcRelation::GreaterOrEqual:
                case CalcRelation::GreaterThan:
                    return Direction::Backward;
                default:
                    return Direction::Neutral;
            }
        };
        auto strictnessOf = [](CalcRelation r) -> Strictness {
            switch (r) {
                case CalcRelation::Equality:
                    return Strictness::Equality;
                case CalcRelation::LessOrEqual:
                case CalcRelation::GreaterOrEqual:
                    return Strictness::Weak;
                case CalcRelation::LessThan:
                case CalcRelation::GreaterThan:
                    return Strictness::Strict;
            }
            return Strictness::Equality;
        };
        auto relationSymbol = [](CalcRelation r) -> const char* {
            switch (r) {
                case CalcRelation::Equality:        return "=";
                case CalcRelation::LessOrEqual:     return "≤";
                case CalcRelation::LessThan:        return "<";
                case CalcRelation::GreaterOrEqual:  return "≥";
                case CalcRelation::GreaterThan:     return ">";
            }
            return "?";
        };

        struct StepRecord {
            CalcRelation relation;
            ExpressionPointer proof;
        };
        std::vector<StepRecord> steps;
        std::vector<ExpressionPointer> endpointKernels;
        endpointKernels.push_back(previousKernel);

        for (size_t k = 0; k < calc.steps.size(); ++k) {
            const auto& step = calc.steps[k];
            Frame stepFrame(*this,
                "calc step " + std::to_string(k + 1)
                + " at line " + std::to_string(step.line),
                localBinders,
                // No goal snapshot here: the step's previous endpoint is
                // not the step's goal, and printing it as `goal:` misleads.
                // The concrete step goal is reported by the error message
                // itself (and the enclosing calc-block frame).
                nullptr,
                step.line, /*column*/ 0);
            ExpressionPointer nextKernel = elaborateExpression(
                *step.nextExpression, localBinders, carrierType);
            // Build the step's expected proof type from its relation.
            // For ≥/> the relation's arguments are flipped (a ≥ b is
            // proved as b ≤ a; a > b is proved as b < a).
            ExpressionPointer stepRelationType;
            Direction stepDirection = directionOf(step.relation);
            Strictness stepStrictness = strictnessOf(step.relation);
            if (step.relation == CalcRelation::Equality) {
                stepRelationType = makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Equality", {carrierLevel}),
                            carrierType),
                        previousKernel),
                    nextKernel);
            } else {
                ExpressionPointer lhs =
                    (stepDirection == Direction::Backward)
                        ? nextKernel : previousKernel;
                ExpressionPointer rhs =
                    (stepDirection == Direction::Backward)
                        ? previousKernel : nextKernel;
                std::string relationName;
                if (stepStrictness == Strictness::Strict) {
                    resolveLtNames();
                    relationName = ltRelationName;
                } else {
                    resolveLeqNames();
                    relationName = leqRelationName;
                }
                stepRelationType = makeApplication(
                    makeApplication(
                        makeConstant(relationName), lhs),
                    rhs);
            }
            ExpressionPointer stepProofKernel;
            if (step.stepProof) {
                // Rewrite-under-Σ: a `Sum(r,f,n) = Sum(r,g,n)` step whose
                // `by` proof is the pointwise `(i) => f(i) = g(i)` desugars
                // to `Sum.extensional`. Tried first; nullptr unless both
                // endpoints are `Sum`s and the proof elaborates pointwise,
                // so it never shadows an ordinary step proof.
                if (step.relation == CalcRelation::Equality) {
                    stepProofKernel = tryUnderBinderStep(
                        localBinders, previousKernel, nextKernel,
                        *step.stepProof, step.line, step.column);
                }
                if (!stepProofKernel) {
                    stepProofKernel = elaborateExpression(
                        *step.stepProof, localBinders, stepRelationType);
                    // `by (<fact>)`: when the proof position elaborates to a
                    // proposition P (its type is the `Proposition` sort) rather
                    // than a proof, the user cited a fact. Prove P and bridge
                    // its proof to the step exactly like `by <proof-of-P>`.
                    bool fromFactCitation = false;
                    if (termIsProposition(localBinders, stepProofKernel)) {
                        stepProofKernel = bridgeCitedFact(
                            stepProofKernel, stepRelationType,
                            localBinders, step.line);
                        fromFactCitation = true;
                    }
                    bool checkThisStep = !fromFactCitation
                        && reportRedundantBy_
                        && !step.stepProofIsExplanation
                        && (step.relation == CalcRelation::Equality
                            || reportRedundantByNonEq_);
                    if (checkThisStep) {
                        ExpressionPointer autoAttempt;
                        RedundancyBudgetGuard budgetGuard(*this);
                        try {
                            if (step.relation == CalcRelation::Equality) {
                                autoAttempt = autoProveCalcStep(
                                    localBinders, previousKernel, nextKernel,
                                    carrierType, carrierLevel,
                                    stepRelationType,
                                    step.line, step.column);
                            } else {
                                // Non-= step (≤/</≥/>): use only the cheap
                                // pattern-matching path (tryContextFactMatch
                                // does a spine-hash lookup over the
                                // environment, then a bounded
                                // autoFillHintForClaim per candidate). Still
                                // expensive for large files — gated behind
                                // --check-redundant-by-non-eq so default
                                // builds don't pay the cost.
                                autoAttempt = tryContextFactMatch(
                                    stepRelationType, localBinders, step.line);
                            }
                        } catch (const ElaborateError&) {
                            autoAttempt = nullptr;
                        } catch (const TypeError&) {
                            autoAttempt = nullptr;
                        }
                        if (autoAttempt) {
                            std::cerr << "warning: " << moduleName_
                                << ":" << step.line << ":" << step.column
                                << ": redundant `by` on calc step — "
                                "auto-prover closes it without help\n";
                        } else {
                          if (step.relation == CalcRelation::Equality) {
                            // Auto-prover couldn't close on its own, but
                            // maybe the user wrote `by congruenceOf(λ, L)`
                            // and `by L` alone would close via the diff-
                            // inference fallback. That catches verbose
                            // congruenceOf wrappers the redundant-by check
                            // misses (because the lemma's preconditions
                            // aren't synthesizable without the user's call).
                            auto* surfApp =
                                std::get_if<SurfaceApplication>(
                                    &step.stepProof->node);
                            if (surfApp && surfApp->arguments.size() == 2) {
                                auto* head =
                                    std::get_if<SurfaceIdentifier>(
                                        &surfApp->function->node);
                                if (head
                                    && head->qualifiedName == "congruenceOf"
                                    && head->universeArgs.empty()) {
                                    ExpressionPointer lemmaKernel;
                                    try {
                                        lemmaKernel = elaborateExpression(
                                            *surfApp->arguments[1].value,
                                            localBinders);
                                    } catch (const ElaborateError&) {
                                        lemmaKernel = nullptr;
                                    } catch (const TypeError&) {
                                        lemmaKernel = nullptr;
                                    }
                                    if (lemmaKernel) {
                                        ExpressionPointer lemmaType;
                                        try {
                                            lemmaType =
                                                inferTypeInLocalContext(
                                                    localBinders,
                                                    lemmaKernel);
                                        } catch (const TypeError&) {
                                            lemmaType = nullptr;
                                        } catch (const ElaborateError&) {
                                            lemmaType = nullptr;
                                        }
                                        ExpressionPointer diffAttempt;
                                        if (lemmaType) {
                                            try {
                                                diffAttempt =
                                                    tryDiffApplyUserProof(
                                                        localBinders,
                                                        previousKernel,
                                                        nextKernel,
                                                        lemmaKernel,
                                                        lemmaType,
                                                        step.line,
                                                        step.column);
                                            } catch (const ElaborateError&) {
                                                diffAttempt = nullptr;
                                            } catch (const TypeError&) {
                                                diffAttempt = nullptr;
                                            }
                                        }
                                        if (diffAttempt) {
                                            std::cerr << "warning: "
                                                << moduleName_ << ":"
                                                << step.line << ":"
                                                << step.column
                                                << ": redundant congruenceOf "
                                                "wrapper — `by <inner lemma>`"
                                                " alone would close this "
                                                "step (diff inference fills "
                                                "the lambda)\n";
                                        }
                                    }
                                }
                            }
                        }
                          }  // end if (step.relation == Equality)
                        // `by L(args)` where `by L` alone (arguments
                        // inferred from the goal, side-conditions discharged
                        // from in-scope hypotheses) would also close the
                        // step — suggest dropping the explicit arguments.
                        // Relation-agnostic: order-lemma side conditions
                        // (e.g. `weaken`) make most discharge cases `≤`/`<`.
                        // Only when the whole `by` isn't already redundant.
                        if (!autoAttempt) {
                            auto* surfApp = std::get_if<SurfaceApplication>(
                                &step.stepProof->node);
                            auto* head = surfApp
                                ? std::get_if<SurfaceIdentifier>(
                                      &surfApp->function->node)
                                : nullptr;
                            if (surfApp && !surfApp->arguments.empty()
                                && head && head->universeArgs.empty()
                                && head->qualifiedName != "congruenceOf"
                                && environment_.lookup(head->qualifiedName)
                                       != nullptr) {
                                ExpressionPointer bareAttempt = nullptr;
                                try {
                                    SurfaceExpressionPointer bare =
                                        makeSurfaceIdentifier(
                                            head->qualifiedName, {},
                                            step.line, step.column);
                                    bareAttempt = elaborateExpression(
                                        *bare, localBinders,
                                        stepRelationType);
                                } catch (const ElaborateError&) {
                                    bareAttempt = nullptr;
                                } catch (const TypeError&) {
                                    bareAttempt = nullptr;
                                }
                                bool valid = false;
                                if (bareAttempt
                                    && !containsFreeVariable(bareAttempt)) {
                                    try {
                                        ExpressionPointer t =
                                            inferTypeInLocalContext(
                                                localBinders, bareAttempt);
                                        ExpressionPointer g =
                                            openOverLocalBinders(
                                                stepRelationType,
                                                localBinders,
                                                localBinders.size());
                                        Context c =
                                            buildContextFromLocalBinders(
                                                localBinders);
                                        valid = isDefinitionallyEqual(
                                            environment_, c, t, g);
                                    } catch (...) { valid = false; }
                                }
                                if (valid) {
                                    std::cerr << "warning: " << moduleName_
                                        << ":" << step.line << ":"
                                        << step.column
                                        << ": arguments to `"
                                        << head->qualifiedName
                                        << "` are inferable from the goal — "
                                           "`by " << head->qualifiedName
                                        << "` alone suffices\n";
                                    // Statistics on where each discharged
                                    // side-condition proof lives (gated, so
                                    // ordinary builds stay quiet).
                                    if (std::getenv("BY_DISCHARGE_STATS")) {
                                        for (const auto& d : lastDischarges_) {
                                            std::cerr << "discharge-stat: "
                                                << moduleName_ << ":"
                                                << step.line
                                                << " lemma="
                                                << head->qualifiedName
                                                << " rel="
                                                << relationSymbol(step.relation)
                                                << " depth=" << std::get<0>(d)
                                                << " total=" << std::get<1>(d)
                                                << " name=" << std::get<2>(d)
                                                << "\n";
                                        }
                                    }
                                }
                            }
                        }
                    }
                }  // end if (!stepProofKernel) — under-Σ took the step otherwise
            } else if (step.relation == CalcRelation::Equality) {
                // Identical path to a by-less `claim a = b`: autoProveClaim
                // runs the equality battery (reflexivity / single-position
                // diff-congruence / AC — the former autoProveCalcStep) as
                // its FIRST tactic and short-circuits, then, only if that
                // fails, the full tactic set (context-fact match, equality
                // bridge, symmetry flip). One path → a calc `=` step and an
                // equality claim never diverge.
                try {
                    stepProofKernel = autoProveClaim(
                        stepRelationType, localBinders, step.line);
                } catch (const AutoProverBudgetError&) {
                    // The auto-prover bailed on effort, not on a genuine
                    // dead end (kernel_quirks #19). Surface the dedicated
                    // "exhausted its budget — add `by`" error rather than
                    // the generic "couldn't close" one.
                    throwAutoProveCalcStepBudgetExceeded(
                        previousKernel, nextKernel, "=",
                        stepRelationType, localBinders);
                } catch (const ElaborateError&) {
                    stepProofKernel = nullptr;
                } catch (const TypeError&) {
                    stepProofKernel = nullptr;
                }
                if (!stepProofKernel) {
                    throwElaborate(
                        "I can't figure out why this calc step is true — "
                        "the auto-prover couldn't close it. Add `by "
                        "<reason>`, or check that the step actually holds."
                        + couldNotProveStepHint(previousKernel, nextKernel,
                              "=", stepRelationType, localBinders));
                }
            } else {
                // Non-equality step (≤/</≥/>) without `by`. Dispatch
                // the step's relation type through the full
                // autoProveClaim — handles hypothesis match, library
                // scan (catches `<T>.LessOrEqual.reflexive` when the
                // endpoints are defeq), conjunction/disjunction
                // intro, contradiction, etc. Equality battery still
                // runs for chains like `b = a ≤ a` whose final step
                // collapses to reflexivity of ≤ at a single point.
                try {
                    stepProofKernel = autoProveClaim(
                        stepRelationType, localBinders, step.line);
                } catch (const AutoProverBudgetError&) {
                    throwAutoProveCalcStepBudgetExceeded(
                        previousKernel, nextKernel,
                        relationSymbol(step.relation),
                        stepRelationType, localBinders);
                } catch (const ElaborateError&) {
                    stepProofKernel = nullptr;
                }
                if (!stepProofKernel) {
                    throwElaborate(
                        std::string("I can't figure out why this calc ")
                        + relationSymbol(step.relation)
                        + " step is true — the auto-prover couldn't close it "
                          "from context. Add `by <reason>`, or check that the "
                          "step actually holds."
                        + couldNotProveStepHint(previousKernel, nextKernel,
                              relationSymbol(step.relation), stepRelationType,
                              localBinders));
                }
            }
            ExpressionPointer stepProofType = inferTypeInLocalContext(
                localBinders, stepProofKernel);
            ExpressionPointer stepRelationTypeOpened = openOverLocalBinders(
                stepRelationType, localBinders, localBinders.size());
            Context stepContext = buildContextFromLocalBinders(localBinders);
            if (!isDefinitionallyEqual(environment_, stepContext,
                                        stepProofType,
                                        stepRelationTypeOpened)) {
                // Auto-rewrite fallback for = steps only.
                ExpressionPointer rewriteAttempt;
                if (step.stepProof
                    && step.relation == CalcRelation::Equality) {
                    try {
                        rewriteAttempt = desugarRewrite(
                            step.stepProof, localBinders,
                            stepRelationType,
                            step.line, step.column);
                    } catch (const ElaborateError&) {
                        rewriteAttempt = nullptr;
                    }
                }
                if (rewriteAttempt) {
                    // Speculative: a malformed rewrite candidate must be
                    // skipped, not type-checked into a "kernel: unbound
                    // internal variable" leak (WS5/WS8). On failure the step
                    // falls through to its surface mismatch error.
                    try {
                        ExpressionPointer rewriteType =
                            inferTypeInLocalContext(localBinders,
                                rewriteAttempt);
                        if (isDefinitionallyEqual(environment_, stepContext,
                                                    rewriteType,
                                                    stepRelationTypeOpened)) {
                            stepProofKernel = rewriteAttempt;
                            stepProofType = rewriteType;
                        }
                    } catch (const TypeError&) {
                    } catch (const ElaborateError&) {
                    }
                }
            }
            // Whole-endpoint reverse (B5): the proof has type `A = B` but
            // the step claims `B = A` — a fold that uses a forward-stated
            // lemma backwards. The structural congruence diff-walk below
            // can't bridge this when the endpoints have different heads and
            // the match needs non-structural defeq (e.g. `Sum(succ k)`
            // unfolding vs an `add`-headed endpoint); a direct symmetry
            // wrap does. This is exactly what writing
            // `Equality.symmetry(?, ?, proof)` by hand achieves, but
            // inferred — tried before the congruence walk because it is a
            // single cheap defeq check and subsumes the most common case.
            if (step.stepProof
                && step.relation == CalcRelation::Equality
                && !isDefinitionallyEqual(environment_, stepContext,
                                            stepProofType,
                                            stepRelationTypeOpened)) {
                try {
                    ExpressionPointer proofTypeWhnf = weakHeadNormalForm(
                        environment_, stepProofType);
                    EqualityComponents components =
                        extractEqualityComponents(
                            proofTypeWhnf, "calc step reverse", step.line);
                    // The proof proves A = B; the step would need B = A.
                    ExpressionPointer reversedType = makeApplication(
                        makeApplication(
                            makeApplication(
                                makeConstant("Equality",
                                    {components.carrierUniverseLevel}),
                                components.carrierType),
                            components.rightEndpoint),
                        components.leftEndpoint);
                    if (isDefinitionallyEqual(environment_, stepContext,
                                                reversedType,
                                                stepRelationTypeOpened)) {
                        ExpressionPointer symmetryCall = makeConstant(
                            "Equality.symmetry",
                            {components.carrierUniverseLevel});
                        symmetryCall = makeApplication(std::move(symmetryCall),
                            closeOverLocalBinders(components.carrierType,
                                localBinders, localBinders.size()));
                        symmetryCall = makeApplication(std::move(symmetryCall),
                            closeOverLocalBinders(components.leftEndpoint,
                                localBinders, localBinders.size()));
                        symmetryCall = makeApplication(std::move(symmetryCall),
                            closeOverLocalBinders(components.rightEndpoint,
                                localBinders, localBinders.size()));
                        symmetryCall = makeApplication(std::move(symmetryCall),
                            stepProofKernel);
                        stepProofKernel = symmetryCall;
                        stepProofType = inferTypeInLocalContext(
                            localBinders, stepProofKernel);
                    }
                } catch (const ElaborateError&) {
                } catch (const TypeError&) {
                }
            }
            // Diff-inference fallback: if the user's `by <proof>` has
            // type Equality(T, a, b) and the calc step's
            // (previousKernel, nextKernel) differ in a single slot at
            // (a, b), wrap with Equality.congruence. Lets the user
            // write `by lemma` instead of
            // `by congruenceOf(λm. <giant context>, lemma)`.
            if (step.stepProof
                && step.relation == CalcRelation::Equality
                && !isDefinitionallyEqual(environment_, stepContext,
                                            stepProofType,
                                            stepRelationTypeOpened)) {
                ExpressionPointer diffAttempt;
                try {
                    diffAttempt = tryDiffApplyUserProof(
                        localBinders, previousKernel, nextKernel,
                        stepProofKernel, stepProofType,
                        step.line, step.column);
                } catch (const ElaborateError&) {
                    diffAttempt = nullptr;
                } catch (const TypeError&) {
                    diffAttempt = nullptr;
                }
                if (diffAttempt) {
                    // Same guard as the rewrite fallback: a malformed diff
                    // candidate is skipped, never leaked (WS5/WS8).
                    try {
                        ExpressionPointer diffAttemptType =
                            inferTypeInLocalContext(localBinders,
                                diffAttempt);
                        if (isDefinitionallyEqual(environment_, stepContext,
                                                    diffAttemptType,
                                                    stepRelationTypeOpened)) {
                            stepProofKernel = diffAttempt;
                            stepProofType = diffAttemptType;
                        }
                    } catch (const TypeError&) {
                    } catch (const ElaborateError&) {
                    }
                }
            }
            if (!isDefinitionallyEqual(environment_, stepContext,
                                        stepProofType,
                                        stepRelationTypeOpened)) {
                // The elaborator itself just found this mismatch (the
                // isDefinitionallyEqual above) — so it owns the message.
                // Report it as mathematics rather than laundering it
                // through rethrowKernelError's "kernel: " path (WS1).
                throwElaborate(
                    "this step's justification proves a different relation "
                    "than the step claims\n"
                    "    this step claims:    "
                    + prettyPrintForDisplay(stepRelationTypeOpened) + "\n"
                    "    but its proof shows: "
                    + prettyPrintForDisplay(stepProofType));
            }
            steps.push_back({step.relation, stepProofKernel});
            endpointKernels.push_back(nextKernel);
            previousKernel = nextKernel;
        }

        // Optional check: look for redundant intermediate calc steps.
        // For each internal step (one that isn't the first or last
        // endpoint), see whether the auto-prover can close the
        // combined neighbouring step directly. If yes, warn — the
        // user can usually delete the intermediate `= midpoint` line
        // without losing kernel acceptance. Restricted to all-`=`
        // adjacent pairs for now (mixed `=`/`≤`/`<` combinations need
        // per-case relation arithmetic). Off by default — the
        // auto-prover dispatch is expensive on long chains.
        if (reportRedundantCalcSteps_) {
            for (size_t k = 1; k + 1 <= steps.size(); ++k) {
                // steps[k-1] takes endpointKernels[k-1] -> endpointKernels[k].
                // steps[k]   takes endpointKernels[k]   -> endpointKernels[k+1].
                // We're asking: can the auto-prover close endpointKernels[k-1]
                // (= endpointKernels[k+1]) directly? Only check when both
                // steps are Equality so the combined relation is unambiguous.
                if (steps[k - 1].relation != CalcRelation::Equality
                    || steps[k].relation != CalcRelation::Equality) {
                    continue;
                }
                ExpressionPointer combinedRelation = makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Equality", {carrierLevel}),
                            carrierType),
                        endpointKernels[k - 1]),
                    endpointKernels[k + 1]);
                ExpressionPointer autoAttempt;
                {
                    // Cap the budget so collapsing is only suggested when the
                    // combined step stays cheap (a costly re-proof means the
                    // intermediate is pulling its weight).
                    RedundancyBudgetGuard budgetGuard(*this);
                    try {
                        autoAttempt = autoProveCalcStep(
                            localBinders,
                            endpointKernels[k - 1],
                            endpointKernels[k + 1],
                            carrierType, carrierLevel,
                            combinedRelation,
                            calc.steps[k - 1].line, calc.steps[k - 1].column);
                    } catch (const ElaborateError&) {
                        autoAttempt = nullptr;
                    } catch (const TypeError&) {
                        autoAttempt = nullptr;
                    }
                }
                if (autoAttempt) {
                    // The redundant ENDPOINT is endpointKernels[k] — it's
                    // the target of steps[k-1] and is written on that
                    // step's line. Removing that line collapses steps
                    // (k-1, k) into one step from endpoint (k-1) to
                    // endpoint (k+1), which the auto-prover can close.
                    std::cerr << "warning: " << moduleName_
                        << ":" << calc.steps[k - 1].line
                        << ":" << calc.steps[k - 1].column
                        << ": calc intermediate target at this line is "
                        "redundant — removing it lets the auto-prover "
                        "close the combined step (next endpoint at line "
                        << calc.steps[k].line << ")\n";
                }
            }
        }

        // Determine overall chain direction and strictness.
        Direction chainDirection = Direction::Neutral;
        Strictness chainStrictness = Strictness::Equality;
        for (const auto& s : steps) {
            Direction d = directionOf(s.relation);
            Strictness st = strictnessOf(s.relation);
            if (d != Direction::Neutral) {
                if (chainDirection == Direction::Neutral) {
                    chainDirection = d;
                } else if (chainDirection != d) {
                    throwElaborate(
                        "calc chain mixes forward (<, ≤) and backward "
                        "(>, ≥) inequalities — only = is allowed in "
                        "either direction");
                }
            }
            if (st == Strictness::Strict) {
                chainStrictness = Strictness::Strict;
            } else if (st == Strictness::Weak
                       && chainStrictness != Strictness::Strict) {
                chainStrictness = Strictness::Weak;
            }
        }

        // Helper: upgrade an =-proof to a ≤-proof via transport on the
        // relation's right argument. Given p : a = b, returns p' :
        // a ≤ b built as transport_proposition(T, λz. a ≤ z, a, b, p,
        // reflexive(a)). The `aExpr` reference inside the motive lambda
        // body needs its De Bruijn indices shifted up by one to account
        // for the new `z` binder we're putting around it.
        auto upgradeEqualityToLessOrEqual =
            [&](ExpressionPointer eqProof,
                ExpressionPointer aExpr,
                ExpressionPointer bExpr) -> ExpressionPointer {
            resolveLeqNames();
            ExpressionPointer aExprShifted = shift(aExpr, 1);
            ExpressionPointer motiveBody = makeApplication(
                makeApplication(
                    makeConstant(leqRelationName),
                    std::move(aExprShifted)),
                makeBoundVariable(0));
            ExpressionPointer motive = makeLambda(
                "z", carrierType, std::move(motiveBody));
            ExpressionPointer reflexive = makeApplication(
                makeConstant(leqReflexiveName), aExpr);
            ExpressionPointer call = makeConstant(
                "Equality.transport_proposition", {carrierLevel});
            call = makeApplication(std::move(call), carrierType);
            call = makeApplication(std::move(call), std::move(motive));
            call = makeApplication(std::move(call), aExpr);
            call = makeApplication(std::move(call), bExpr);
            call = makeApplication(std::move(call), std::move(eqProof));
            call = makeApplication(std::move(call), std::move(reflexive));
            return call;
        };

        // Normalize for Backward chains: reverse endpoint and step
        // order. Each Backward ≥/> step's proof already has type
        // matching the normalized direction (a ≥ b's proof is b ≤ a,
        // exactly what the reversed walk wants going from b to a).
        // But Backward = steps were elaborated with type
        // `previous = next` (user-direction); the normalized walk
        // needs `next = previous`, so we flip them via
        // Equality.symmetry.
        std::vector<ExpressionPointer> normalizedEndpoints =
            endpointKernels;
        std::vector<StepRecord> normalizedSteps = steps;
        if (chainDirection == Direction::Backward) {
            std::reverse(normalizedEndpoints.begin(),
                          normalizedEndpoints.end());
            std::reverse(normalizedSteps.begin(),
                          normalizedSteps.end());
            for (size_t k = 0; k < normalizedSteps.size(); ++k) {
                if (normalizedSteps[k].relation
                    != CalcRelation::Equality) {
                    continue;
                }
                // normalizedSteps[k] corresponds to user's step
                // (N-1-k), whose endpoints are
                // (endpointKernels[N-1-k], endpointKernels[N-k]) =
                // (normalizedEndpoints[k+1], normalizedEndpoints[k]).
                // Build symmetry over the user-direction endpoints.
                ExpressionPointer call = makeConstant(
                    "Equality.symmetry", {carrierLevel});
                call = makeApplication(std::move(call), carrierType);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k + 1]);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k]);
                call = makeApplication(std::move(call),
                    normalizedSteps[k].proof);
                normalizedSteps[k].proof = std::move(call);
            }
        }

        // All-= chain: fold via Equality.transitivity (unchanged).
        if (chainStrictness == Strictness::Equality) {
            if (normalizedSteps.size() == 1) {
                return normalizedSteps[0].proof;
            }
            ExpressionPointer running = normalizedSteps[0].proof;
            for (size_t k = 1; k < normalizedSteps.size(); ++k) {
                ExpressionPointer call = makeConstant(
                    "Equality.transitivity", {carrierLevel});
                call = makeApplication(std::move(call), carrierType);
                call = makeApplication(std::move(call), normalizedEndpoints[0]);
                call = makeApplication(std::move(call), normalizedEndpoints[k]);
                call = makeApplication(std::move(call), normalizedEndpoints[k + 1]);
                call = makeApplication(std::move(call), std::move(running));
                call = makeApplication(std::move(call), normalizedSteps[k].proof);
                running = std::move(call);
            }
            return running;
        }

        // Chain has at least one ≤ or <. Process each step's proof into
        // its working form: = becomes ≤ via transport; ≤ stays ≤; < stays <.
        // Track the running proof's strictness as we fold.
        auto stepProofAsLeq = [&](size_t k) -> ExpressionPointer {
            const auto& s = normalizedSteps[k];
            if (strictnessOf(s.relation) == Strictness::Equality) {
                return upgradeEqualityToLessOrEqual(
                    s.proof,
                    normalizedEndpoints[k],
                    normalizedEndpoints[k + 1]);
            }
            // ≤ or < step: kept as-is at this point; composition will
            // pick the right transitive lemma based on strictness.
            return s.proof;
        };

        // Single-step calc: the (possibly upgraded) step proof IS the
        // result. If the chain strictness exceeds the step's, we have
        // to upgrade =-only to ≤ (chain Weak), but a single-step chain
        // can't be Strict from an = step alone.
        if (normalizedSteps.size() == 1) {
            if (strictnessOf(normalizedSteps[0].relation)
                == Strictness::Equality) {
                return stepProofAsLeq(0);
            }
            return normalizedSteps[0].proof;
        }

        // Weak-only chain (no <): compose via <T>.LessOrEqual.transitive.
        if (chainStrictness == Strictness::Weak) {
            ExpressionPointer running = stepProofAsLeq(0);
            for (size_t k = 1; k < normalizedSteps.size(); ++k) {
                ExpressionPointer nextProof = stepProofAsLeq(k);
                ExpressionPointer call =
                    makeConstant(leqTransitiveName);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[0]);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k]);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k + 1]);
                if (transitiveTakesProofsSwapped) {
                    call = makeApplication(std::move(call),
                        std::move(nextProof));
                    call = makeApplication(std::move(call),
                        std::move(running));
                } else {
                    call = makeApplication(std::move(call),
                        std::move(running));
                    call = makeApplication(std::move(call),
                        std::move(nextProof));
                }
                running = std::move(call);
            }
            return running;
        }

        // Strict chain (some step is <): the running proof becomes
        // strict the first time a < step is hit, and stays strict.
        // Compose using <T>.LessThan.transitive_{left,right} plus
        // weaken as appropriate.
        auto weakenStrict =
            [&](ExpressionPointer xExpr, ExpressionPointer yExpr,
                ExpressionPointer strictProof) -> ExpressionPointer {
            ExpressionPointer call = makeConstant(ltWeakenName);
            call = makeApplication(std::move(call), xExpr);
            call = makeApplication(std::move(call), yExpr);
            call = makeApplication(std::move(call),
                std::move(strictProof));
            return call;
        };
        ExpressionPointer running;
        Strictness runningStrictness;
        if (strictnessOf(normalizedSteps[0].relation)
            == Strictness::Strict) {
            running = normalizedSteps[0].proof;
            runningStrictness = Strictness::Strict;
        } else {
            running = stepProofAsLeq(0);
            runningStrictness = Strictness::Weak;
        }
        for (size_t k = 1; k < normalizedSteps.size(); ++k) {
            Strictness stepKind =
                strictnessOf(normalizedSteps[k].relation);
            ExpressionPointer stepProof;
            if (stepKind == Strictness::Strict) {
                stepProof = normalizedSteps[k].proof;
            } else {
                // Equality or Weak: upgrade to ≤ form.
                stepProof = stepProofAsLeq(k);
            }
            ExpressionPointer xExpr = normalizedEndpoints[0];
            ExpressionPointer yExpr = normalizedEndpoints[k];
            ExpressionPointer zExpr = normalizedEndpoints[k + 1];
            if (runningStrictness == Strictness::Weak
                && stepKind != Strictness::Strict) {
                // weak ⋈ weak (incl. =-upgraded) → weak.
                ExpressionPointer call =
                    makeConstant(leqTransitiveName);
                call = makeApplication(std::move(call), xExpr);
                call = makeApplication(std::move(call), yExpr);
                call = makeApplication(std::move(call), zExpr);
                if (transitiveTakesProofsSwapped) {
                    call = makeApplication(std::move(call),
                        std::move(stepProof));
                    call = makeApplication(std::move(call),
                        std::move(running));
                } else {
                    call = makeApplication(std::move(call),
                        std::move(running));
                    call = makeApplication(std::move(call),
                        std::move(stepProof));
                }
                running = std::move(call);
            } else if (runningStrictness == Strictness::Weak
                       && stepKind == Strictness::Strict) {
                // weak ⋈ strict → strict via transitive_left(le, lt).
                ExpressionPointer call =
                    makeConstant(ltTransitiveLeftName);
                call = makeApplication(std::move(call), xExpr);
                call = makeApplication(std::move(call), yExpr);
                call = makeApplication(std::move(call), zExpr);
                call = makeApplication(std::move(call),
                    std::move(running));
                call = makeApplication(std::move(call),
                    std::move(stepProof));
                running = std::move(call);
                runningStrictness = Strictness::Strict;
            } else if (runningStrictness == Strictness::Strict
                       && stepKind != Strictness::Strict) {
                // strict ⋈ weak (incl. =-upgraded) → strict via
                // transitive_right(lt, le).
                ExpressionPointer call =
                    makeConstant(ltTransitiveRightName);
                call = makeApplication(std::move(call), xExpr);
                call = makeApplication(std::move(call), yExpr);
                call = makeApplication(std::move(call), zExpr);
                call = makeApplication(std::move(call),
                    std::move(running));
                call = makeApplication(std::move(call),
                    std::move(stepProof));
                running = std::move(call);
            } else {
                // strict ⋈ strict → strict via
                // transitive_left(weaken(running), step).
                ExpressionPointer weakened =
                    weakenStrict(xExpr, yExpr, std::move(running));
                ExpressionPointer call =
                    makeConstant(ltTransitiveLeftName);
                call = makeApplication(std::move(call), xExpr);
                call = makeApplication(std::move(call), yExpr);
                call = makeApplication(std::move(call), zExpr);
                call = makeApplication(std::move(call),
                    std::move(weakened));
                call = makeApplication(std::move(call),
                    std::move(stepProof));
                running = std::move(call);
            }
        }
        return running;
    }

bool Elaborator::decomposeBinaryOpApplication(
        ExpressionPointer term,
        std::string& outOpName,
        std::vector<LevelPointer>& outOpUniverseArguments,
        ExpressionPointer& outLeft,
        ExpressionPointer& outRight) {
        auto* outerApp = std::get_if<Application>(&term->node);
        if (!outerApp) return false;
        auto* innerApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!innerApp) return false;
        auto* opConst =
            std::get_if<Constant>(&innerApp->function->node);
        if (!opConst) return false;
        outOpName = opConst->name;
        outOpUniverseArguments = opConst->universeArguments;
        outLeft = innerApp->argument;
        outRight = outerApp->argument;
        return true;
    }

void Elaborator::registerAlgebraicShape(const std::string& theoremName,
                                  ExpressionPointer typeExpr) {
        registerGenericRewriteLemma(theoremName, typeExpr);
    }

void Elaborator::registerGenericRewriteLemma(const std::string& theoremName,
                                       ExpressionPointer typeExpr) {
        // First-cut: zero-universe-parameter lemmas only.
        const Declaration* declaration =
            environment_.lookup(theoremName);
        if (!declaration) return;
        auto* asDefinition =
            std::get_if<Definition>(declaration);
        if (!asDefinition) return;
        if (!asDefinition->universeParameters.empty()) return;
        // Peel leading Pi binders, collecting each domain in
        // outer-to-inner order.
        std::vector<ExpressionPointer> rawDomains;
        ExpressionPointer cursor = typeExpr;
        while (auto* pi = std::get_if<Pi>(&cursor->node)) {
            rawDomains.push_back(pi->domain);
            cursor = pi->codomain;
        }
        int binderCount = static_cast<int>(rawDomains.size());
        if (binderCount == 0) return;
        // Body must be App(App(App(Equality, carrier), lhs), rhs).
        auto* eqApp3 = std::get_if<Application>(&cursor->node);
        if (!eqApp3) return;
        auto* eqApp2 =
            std::get_if<Application>(&eqApp3->function->node);
        if (!eqApp2) return;
        auto* eqApp1 =
            std::get_if<Application>(&eqApp2->function->node);
        if (!eqApp1) return;
        auto* eqHead = std::get_if<Constant>(&eqApp1->function->node);
        if (!eqHead || eqHead->name != "Equality") return;
        ExpressionPointer lhs = eqApp2->argument;
        ExpressionPointer rhs = eqApp3->argument;
        // Skip trivially-degenerate `(a : T) → a = a` shapes.
        if (std::holds_alternative<BoundVariable>(lhs->node)
            && std::holds_alternative<BoundVariable>(rhs->node)) {
            return;
        }
        // Lift each binder's domain into the conclusion's frame so
        // `instantiateLemmaBinders` can substitute via the binding
        // vector. Pi at peel index k (0 = outermost) has its domain in
        // a frame with k outer binders; the corresponding conclusion-
        // frame index is `binderCount - 1 - k`. The lift amount is
        // `binderCount - k` so that the OUTERMOST binder (peel index 0,
        // conclusion-frame index n-1, no inner BVs in its domain) shifts
        // by n — a no-op on closed domains — and the innermost (peel
        // index n-1, conclusion-frame index 0) shifts by 1 — moving its
        // BV(0..n-2) refs (to outer binders) up to BV(1..n-1).
        std::vector<ExpressionPointer> binderTypes(binderCount);
        for (int peelIdx = 0; peelIdx < binderCount; ++peelIdx) {
            int conclusionIdx = binderCount - 1 - peelIdx;
            binderTypes[conclusionIdx] = liftBoundVariables(
                rawDomains[peelIdx], binderCount - peelIdx, 0);
        }
        // Register both directions. When a side is a bare BoundVariable
        // its spineHash is the wildcard tag, which lands the entry in
        // the wildcard bucket. That bucket is consulted only when the
        // diff position is itself a leaf (a BV/FV/Sort) — so reverse-
        // direction identity entries don't pollute regular lookups.
        RewriteLemma forwardEntry;
        forwardEntry.lemmaName = theoremName;
        forwardEntry.binderCount = binderCount;
        forwardEntry.lhs = lhs;
        forwardEntry.rhs = rhs;
        forwardEntry.binderTypes = binderTypes;
        forwardEntry.reverseDirection = false;
        lemmaIndex_.emplace(spineHash(lhs),
                              std::move(forwardEntry));
        RewriteLemma reverseEntry;
        reverseEntry.lemmaName = theoremName;
        reverseEntry.binderCount = binderCount;
        reverseEntry.lhs = lhs;
        reverseEntry.rhs = rhs;
        reverseEntry.binderTypes = std::move(binderTypes);
        reverseEntry.reverseDirection = true;
        lemmaIndex_.emplace(spineHash(rhs),
                              std::move(reverseEntry));
    }

ExpressionPointer Elaborator::autoProveCalcStep(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        ExpressionPointer stepEqualityType,
        int line, int column) {
        // Self-arm the effort budget when this is entered OUTSIDE a
        // top-level autoProveClaim (e.g. from the redundant-`by` /
        // redundant-calc-step checks, which call us directly). That way
        // even those off-by-default diagnostic paths can't hang on an
        // expensive recursion — they just see the step decline.
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
        if (autoProveBudgetLimit_ > 0 && !autoProveBudgetActive_) {
            autoProveBudgetActive_ = true;
            autoProveBudgetTripped_ = false;
            autoProveStepSnapshot_ = kernelStepsSoFar();
            armedHere = true;
        }
        BudgetGuard budgetGuard{*this, armedHere};
        // The raw step runs a reflexivity conversion check (which can
        // force δ-unfolding an expensive recursion), a structural diff
        // walk, and an AC/ring attempt — each non-trivial. Charge the
        // effort budget so a recursive cascade of calc steps (via
        // proveApplicationDiff) can't thrash unboundedly; throws
        // AutoProverBudgetError once exhausted.
        ExpressionPointer result;
        try {
            autoProveSpend(4);
            result = autoProveCalcStepRaw(
                localBinders, previousKernel, nextKernel,
                carrierType, carrierLevel, stepEqualityType, line, column);
        } catch (const AutoProverBudgetError&) {
            // If THIS frame armed the budget (a direct caller such as the
            // redundant-`by` checks), absorb the trip and decline the step
            // — those diagnostic paths only care whether the auto-prover
            // closes it, not why it stopped. If an enclosing autoProveClaim
            // owns the budget, rethrow so the trip reaches the proof-step
            // dispatch and surfaces the "add `by`" error.
            if (armedHere) return nullptr;
            throw;
        }
        if (!result) return nullptr;
        // A calc-step proof from the auto-prover is built CLOSED over the
        // local binders, so it must contain NO free variables — the local
        // binders appear as de Bruijn indices, top-level names as
        // Constants. A leaked FreeVariable (e.g. an opened-but-not-reclosed
        // carrier like `Group.carrier(@H)`) means the auto-prover assembled
        // an invalid term: the kernel would reject it later with a cryptic
        // "unbound internal variable". Surface it as the auto-prover bug it
        // is, and treat the step as unproven (so the redundant-`by` check
        // doesn't flag a `by` whose removal would fail, and the by-less
        // path reports a clean "couldn't close it" instead).
        if (containsFreeVariable(result)) {
            std::cerr << "warning: " << moduleName_ << ":" << line << ":"
                << column << ": auto-prover produced a calc-step proof with a "
                "leaked free variable — this is an auto-prover bug; treating "
                "the step as unproven\n";
            return nullptr;
        }
        return result;
    }

ExpressionPointer Elaborator::proveApplicationDiff(
        const std::vector<LocalBinder>& localBinders,
        const Application* leftApp,
        const Application* rightApp,
        int line, int column) {
        if (environment_.lookup("Equality.transitivity") == nullptr) {
            return nullptr;
        }
        try {
            ExpressionPointer leftFn = leftApp->function;
            ExpressionPointer rightFn = rightApp->function;
            ExpressionPointer leftArg = leftApp->argument;
            ExpressionPointer rightArg = rightApp->argument;
            auto closedType = [&](ExpressionPointer t) {
                return closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, t),
                    localBinders, localBinders.size());
            };
            auto eqType = [&](LevelPointer lvl, ExpressionPointer ty,
                              ExpressionPointer x, ExpressionPointer y) {
                ExpressionPointer e = makeConstant("Equality", {lvl});
                e = makeApplication(std::move(e), ty);
                e = makeApplication(std::move(e), x);
                e = makeApplication(std::move(e), y);
                return e;
            };
            ExpressionPointer argType = closedType(leftArg);
            LevelPointer argLevel = typeUniverseOf(localBinders, leftArg);
            ExpressionPointer fnType = closedType(leftFn);
            LevelPointer fnLevel = typeUniverseOf(localBinders, leftFn);
            ExpressionPointer appLeft = makeApplication(leftFn, leftArg);
            ExpressionPointer appType = closedType(appLeft);
            LevelPointer appLevel = typeUniverseOf(localBinders, appLeft);

            ExpressionPointer argProof = autoProveCalcStep(
                localBinders, leftArg, rightArg, argType, argLevel,
                eqType(argLevel, argType, leftArg, rightArg), line, column);
            if (!argProof) return nullptr;
            ExpressionPointer fnProof = autoProveCalcStep(
                localBinders, leftFn, rightFn, fnType, fnLevel,
                eqType(fnLevel, fnType, leftFn, rightFn), line, column);
            if (!fnProof) return nullptr;

            // cong1 : leftFn leftArg = leftFn rightArg, motive λz. leftFn z
            ExpressionPointer motive1 = makeLambda("_calc_z", argType,
                makeApplication(liftBoundVariables(leftFn, 1, 0),
                                makeBoundVariable(0)));
            ExpressionPointer cong1 = makeConstant(
                "Equality.congruence", {argLevel, appLevel});
            cong1 = makeApplication(std::move(cong1), argType);
            cong1 = makeApplication(std::move(cong1), appType);
            cong1 = makeApplication(std::move(cong1), std::move(motive1));
            cong1 = makeApplication(std::move(cong1), leftArg);
            cong1 = makeApplication(std::move(cong1), rightArg);
            cong1 = makeApplication(std::move(cong1), std::move(argProof));

            // cong2 : leftFn rightArg = rightFn rightArg, motive λf. f rightArg
            ExpressionPointer motive2 = makeLambda("_calc_f", fnType,
                makeApplication(makeBoundVariable(0),
                                liftBoundVariables(rightArg, 1, 0)));
            ExpressionPointer cong2 = makeConstant(
                "Equality.congruence", {fnLevel, appLevel});
            cong2 = makeApplication(std::move(cong2), fnType);
            cong2 = makeApplication(std::move(cong2), appType);
            cong2 = makeApplication(std::move(cong2), std::move(motive2));
            cong2 = makeApplication(std::move(cong2), leftFn);
            cong2 = makeApplication(std::move(cong2), rightFn);
            cong2 = makeApplication(std::move(cong2), std::move(fnProof));

            // transitivity : leftFn leftArg = rightFn rightArg
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

ExpressionPointer Elaborator::wrapCongruenceChainOutsideIn(
        const std::vector<LocalBinder>& localBinders,
        const std::vector<CalcCongruencePathStep>& pathStepsOutsideIn,
        ExpressionPointer currentLeft,
        ExpressionPointer currentRight,
        ExpressionPointer currentProof) {
        try {
            for (auto iterator = pathStepsOutsideIn.rbegin();
                 iterator != pathStepsOutsideIn.rend(); ++iterator) {
                const CalcCongruencePathStep& step = *iterator;
                LevelPointer varLevel = typeUniverseOf(
                    localBinders, currentLeft);
                ExpressionPointer varType = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, currentLeft),
                    localBinders, localBinders.size());
                ExpressionPointer lambdaBody;
                ExpressionPointer outerLeft, outerRight;
                if (step.kind == CalcCongruencePathStep::Kind::Arg) {
                    ExpressionPointer liftedFunction =
                        liftBoundVariables(step.savedSide, 1, 0);
                    lambdaBody = makeApplication(
                        std::move(liftedFunction), makeBoundVariable(0));
                    outerLeft = makeApplication(step.savedSide, currentLeft);
                    outerRight = makeApplication(step.savedSide, currentRight);
                } else {
                    ExpressionPointer liftedArgument =
                        liftBoundVariables(step.savedSide, 1, 0);
                    lambdaBody = makeApplication(
                        makeBoundVariable(0), std::move(liftedArgument));
                    outerLeft = makeApplication(currentLeft, step.savedSide);
                    outerRight = makeApplication(currentRight, step.savedSide);
                }
                ExpressionPointer lambda = makeLambda(
                    "_calc_z", varType, std::move(lambdaBody));
                LevelPointer outerLevel = typeUniverseOf(
                    localBinders, outerLeft);
                ExpressionPointer outerType = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, outerLeft),
                    localBinders, localBinders.size());
                ExpressionPointer call = makeConstant(
                    "Equality.congruence", {varLevel, outerLevel});
                call = makeApplication(std::move(call), varType);
                call = makeApplication(std::move(call), outerType);
                call = makeApplication(std::move(call), std::move(lambda));
                call = makeApplication(std::move(call), currentLeft);
                call = makeApplication(std::move(call), currentRight);
                call = makeApplication(std::move(call), std::move(currentProof));
                currentProof = std::move(call);
                currentLeft = std::move(outerLeft);
                currentRight = std::move(outerRight);
            }
        } catch (const TypeError&) {
            return nullptr;
        } catch (const ElaborateError&) {
            return nullptr;
        }
        return currentProof;
    }

ExpressionPointer Elaborator::autoProveCalcStepRaw(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        ExpressionPointer stepEqualityType,
        int line, int column) {
        (void)stepEqualityType;
        // Strategy 2 below wraps with Equality.congruence. If that name
        // isn't declared (small test modules sometimes omit it), we'd
        // build a term referencing an undefined constant. Only the
        // pure-reflexivity strategy 1 below is safe in that case — and
        // it's cheap to keep, so we keep going past this point but skip
        // strategy 2 below.
        const bool congruenceAvailable =
            environment_.lookup("Equality.congruence") != nullptr;
        // ζ-unfold local let-binders so the structural matchers
        // (tryClassifyDiff path-walk, lemma index) see through surface
        // abbreviations. The kernel-level Equality at the original
        // endpoints is ζ-equal to the Equality at the unfolded
        // endpoints, so a proof for the unfolded form is also a proof
        // for the original (verified by the post-elaboration
        // isDefinitionallyEqual check against the original stepRelation
        // type, which now also sees let-values via ContextEntry.value).
        previousKernel = zetaUnfoldLetBinders(previousKernel, localBinders);
        nextKernel = zetaUnfoldLetBinders(nextKernel, localBinders);
        // Strategy 1: reflexivity for definitionally-equal endpoints.
        Context openedContext = buildContextFromLocalBinders(localBinders);
        ExpressionPointer previousOpened = openOverLocalBinders(
            previousKernel, localBinders, localBinders.size());
        ExpressionPointer nextOpened = openOverLocalBinders(
            nextKernel, localBinders, localBinders.size());
        if (isDefinitionallyEqual(environment_, openedContext,
                                    previousOpened, nextOpened)) {
            ExpressionPointer call =
                makeConstant("reflexivity", {carrierLevel});
            call = makeApplication(std::move(call), carrierType);
            call = makeApplication(std::move(call), previousKernel);
            return call;
        }
        // Strategy 2: single-position diff classification. Walk both
        // sides in lockstep through Application nodes. At each App
        // level there are three possibilities: function parts equal
        // (descend into argument), arguments equal (descend into
        // function), or both differ (bail). We collect a list of
        // path steps and reconstruct the proof inside-out with
        // Equality.congruence wrappers.
        // Skip strategy 2 entirely if Equality.congruence isn't in
        // scope — the wrappers below would reference an undefined
        // constant, and the eventual kernel error wouldn't carry
        // calc-step attribution.
        if (!congruenceAvailable) {
            return nullptr;
        }
        std::vector<CalcCongruencePathStep> pathStepsOutsideIn;
        ExpressionPointer leftCursor = previousKernel;
        ExpressionPointer rightCursor = nextKernel;
        ExpressionPointer innerProof = nullptr;
        // At every level we first try to classify the current pair
        // directly (commutativity / associativity / identity / local-
        // hypothesis). Only descend if no classifier fires. This lets a
        // local hypothesis whose endpoints sit at some intermediate
        // level match without us descending past it.
        while (true) {
            innerProof = tryClassifyDiff(
                localBinders, openedContext, leftCursor, rightCursor);
            if (innerProof) break;
            auto* leftApp =
                std::get_if<Application>(&leftCursor->node);
            auto* rightApp =
                std::get_if<Application>(&rightCursor->node);
            if (!leftApp || !rightApp) break;
            bool functionEqual = structurallyEqual(
                leftApp->function, rightApp->function);
            bool argumentEqual = structurallyEqual(
                leftApp->argument, rightApp->argument);
            if (functionEqual && argumentEqual) {
                return nullptr;
            }
            if (functionEqual) {
                pathStepsOutsideIn.push_back(
                    {CalcCongruencePathStep::Kind::Arg, leftApp->function});
                leftCursor = leftApp->argument;
                rightCursor = rightApp->argument;
                continue;
            }
            if (argumentEqual) {
                pathStepsOutsideIn.push_back(
                    {CalcCongruencePathStep::Kind::Fn, leftApp->argument});
                leftCursor = leftApp->function;
                rightCursor = rightApp->function;
                continue;
            }
            // Both function and argument differ at this level. Prove the
            // two sub-equalities recursively and combine (congruence +
            // transitivity); break with the combined proof (or nullptr if
            // a sub-proof failed) for the path-step reconstruction below.
            innerProof = proveApplicationDiff(
                localBinders, leftApp, rightApp, line, column);
            break;
        }
        if (!innerProof) {
            // Phase-2 fallback: try AC rearrangement via the existing
            // `ring` proof emitter on the full goal. This catches
            // multi-position commutative / associative shuffles like
            // `(a + b) + (c + d) = (b + a) + (d + c)` that the
            // single-position walker bails on.
            ExpressionPointer ringProof = tryAcRearrangement(
                localBinders, previousKernel, nextKernel,
                carrierType, carrierLevel, line);
            if (ringProof) return ringProof;
            return nullptr;
        }
        // Wrap from innermost out. At each step we need the type of
        // the "varying side" (lambda domain) and the type of the
        // result of applying the lambda (lambda codomain). We use
        // inferTypeInLocalContext and typeUniverseOf to compute them
        // — if either throws, bail.
        ExpressionPointer currentProof = wrapCongruenceChainOutsideIn(
            localBinders, pathStepsOutsideIn, leftCursor, rightCursor,
            innerProof);
        (void)carrierType;
        (void)carrierLevel;
        return currentProof;
    }

void Elaborator::checkRedundantCongruenceOfWrapper(
        const SurfaceExpressionPointer& surfaceExpression,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedTypeClosed,
        const std::string& positionLabel) {
        if (!reportRedundantBy_ || !surfaceExpression
            || !expectedTypeClosed) return;
        auto* surfApp = std::get_if<SurfaceApplication>(
            &surfaceExpression->node);
        if (!surfApp || surfApp->arguments.size() != 2) return;
        auto* head = std::get_if<SurfaceIdentifier>(
            &surfApp->function->node);
        if (!head || head->qualifiedName != "congruenceOf"
            || !head->universeArgs.empty()) return;
        ExpressionPointer innerKernel;
        try {
            innerKernel = elaborateExpression(
                *surfApp->arguments[1].value, localBinders);
        } catch (const ElaborateError&) { return; }
          catch (const TypeError&) { return; }
        if (!innerKernel) return;
        ExpressionPointer coerced = coerceToExpectedTypeViaDiff(
            localBinders, innerKernel, expectedTypeClosed);
        if (coerced == innerKernel) return;
        ExpressionPointer coercedType;
        try {
            coercedType = inferTypeInLocalContext(
                localBinders, coerced);
        } catch (const TypeError&) { return; }
          catch (const ElaborateError&) { return; }
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        if (isDefinitionallyEqual(environment_, openedContext,
                       coercedType, expectedOpened)) {
            std::cerr << "warning: " << moduleName_ << ":"
                << surfaceExpression->line << ":"
                << surfaceExpression->column
                << ": redundant congruenceOf wrapper at "
                << positionLabel
                << " — the inner lemma alone would close the goal "
                "(diff inference fills the lambda)\n";
        }
    }


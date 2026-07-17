// Out-of-line Elaborator method definitions: the calc tactic (calc / calc-over-preorder + per-step diff proving)
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::elaborateCalc(
        const SurfaceCalc& calc,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        // ONE fold for every relation (PLAN_CALC_WIDENING §D). `=`/≤/<
        // (and their flipped ≥/> spellings) and the named relations
        // (`∣`, `⊆`, `≈`, `∈`) are all steps of the same left fold:
        // `=` composes with everything by transport, same-relation
        // steps by the relation's transitivity lemma, and the mixed
        // ≤/< pairs by the relation-composition table in pass 2 below.
        ++calcDepth_;
        struct CalcDepthGuard { int& d; ~CalcDepthGuard() { --d; } }
            calcDepthGuard{calcDepth_};
        Frame frame(*this,
            "calc block at line " + std::to_string(line),
            localBinders, expectedType, line, column);
        ExpressionPointer previousKernel = elaborateExpression(
            *calc.initialExpression, localBinders);
        ExpressionPointer carrierTypeOpen =
            inferTypeInLocalContext(localBinders, previousKernel);
        // The carrier comes from the FIRST RELATION, not the leading term in
        // isolation: a bare-numeral leading term (`0`) defaults to Natural,
        // but the relation's other operand may pin a richer carrier (Real).
        // Join the two operand types and lift the leading term up the
        // coercion tower — exactly the reconciliation each later step gets
        // (the `combineOperands` block in the fold below) — so `calc 0 ≤
        // abs(x) …` elaborates `0` at the carrier `abs(x)` lives in. (Only
        // the leading-term lift is done here; a lower-tower RHS is lifted by
        // the fold.)
        if (!calc.steps.empty()) {
            // Best-effort: probe the first relation's right operand for its
            // carrier. It is re-elaborated properly (with the carrier as the
            // expected type) in the fold below, so if it cannot stand alone
            // here — e.g. a `Sum.left(x)` whose other type argument is only
            // fixed by the expected type — fall back to the leading term's
            // carrier rather than letting the probe's failure escape.
            std::string leadingHead = headConstantName(carrierTypeOpen);
            std::string firstRightHead;
            ExpressionPointer firstRightTypeOpen = nullptr;
            try {
                ExpressionPointer firstRightKernel = elaborateExpression(
                    *calc.steps[0].nextExpression, localBinders);
                firstRightTypeOpen =
                    inferTypeInLocalContext(localBinders, firstRightKernel);
                firstRightHead = headConstantName(firstRightTypeOpen);
            } catch (const std::exception&) {
                firstRightHead.clear();
                firstRightTypeOpen = nullptr;
            }
            if (firstRightTypeOpen
                && !leadingHead.empty() && !firstRightHead.empty()
                && leadingHead != firstRightHead) {
                ExpressionPointer leadingTypeClosed = closeOverLocalBinders(
                    carrierTypeOpen, localBinders, localBinders.size());
                ExpressionPointer firstRightTypeClosed = closeOverLocalBinders(
                    firstRightTypeOpen, localBinders, localBinders.size());
                if (auto combined = combineOperands(
                        leadingHead, firstRightHead,
                        leadingTypeClosed, firstRightTypeClosed)) {
                    if (!combined->coerceLeft.empty()) {
                        previousKernel = applyCoercionChain(
                            std::move(previousKernel), combined->coerceLeft);
                        previousKernel = castPushToLeaves(
                            previousKernel, localBinders).term;
                        carrierTypeOpen = inferTypeInLocalContext(
                            localBinders, previousKernel);
                    }
                }
            }
        }
        ExpressionPointer carrierType = closeOverLocalBinders(
            carrierTypeOpen, localBinders, localBinders.size());
        LevelPointer carrierLevel =
            typeUniverseOf(localBinders, previousKernel);

        // Resolve the carrier's <T>.LessOrEqual and <T>.LessThan
        // relations lazily, on first use (their composition lemmas —
        // transitive / transitive_left / transitive_right / weaken —
        // hang off the relation name via the pass-2 registry). The
        // operator registry — populated by `operator (≤) on (T, T) :=
        // <T>.LessOrEqual;` and the parallel `<`/`>`/`≥` registrations —
        // drives the name lookup. Natural has no namespaced wrapper
        // around its inductive `LessOrEqual` below Natural/order.math,
        // so we fall back to bare `LessOrEqual` for it.
        // `headConstantName` (not a bare Constant probe): parameterised
        // carriers like `Set(Natural)` name their head (`Set`), which
        // the named-relation registry keys on.
        std::string carrierTypeName = headConstantName(carrierTypeOpen);
        std::string leqRelationName;       // e.g. "Real.LessOrEqual"
        bool transitiveTakesProofsSwapped = false;
        std::string ltRelationName;        // e.g. "Real.LessThan"
        auto resolveLeqNames = [&]() {
            if (!leqRelationName.empty()) return;
            std::string registered = environment_.lookupOperator(
                "≤", carrierTypeName, carrierTypeName);
            if (!registered.empty()) {
                leqRelationName = registered;
            } else if (carrierTypeName == "Natural") {
                // Natural's ≤ falls back to the bare inductive
                // `LessOrEqual`. Its transitive lemma takes the proofs
                // in (b≤c, a≤b) order — historical accident from the
                // pattern-match-on-second-proof construction — so flag
                // the swap for the composition step below.
                leqRelationName = "LessOrEqual";
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
        };

        // Resolve a NAMED relation (`∣`, `⊆`, `≈`, `∈`) via the operator
        // registry: `leftTypeClosed` is the LEFT operand's type (the
        // anchor for leading-implicit inference, e.g. the `{T}` of
        // `Set.member`), `rightHead` the right operand's type head —
        // the carrier itself for a homogeneous relation, `Set` for `∈`.
        // Returns the resolved function name and its ready-to-apply
        // head (`head x y : Proposition`).
        auto resolveNamedRelation = [&](const std::string& symbol,
                                        ExpressionPointer leftTypeClosed,
                                        const std::string& rightHead)
                -> std::pair<std::string, ExpressionPointer> {
            std::string leftHead = headConstantName(leftTypeClosed);
            std::string relationFn = environment_.lookupOperator(
                symbol, leftHead, rightHead);
            if (relationFn.empty() && leftHead == "Natural"
                && symbol == "∣") {
                // Foundational Natural modules use `∣` below the
                // operator-registration file.
                relationFn = "Natural.divides";
            }
            if (relationFn.empty()) {
                throwElaborate(
                    "calc step uses '" + symbol + "' but no such relation "
                    "is available on " + (leftHead.empty()
                        ? std::string("this carrier") : leftHead)
                    + " — register one via `operator (" + symbol + ") on ("
                    + leftHead + ", " + rightHead + ") := <fn>;`");
            }
            ExpressionPointer head = applyOperatorImplicitFillers(
                makeConstant(relationFn), relationFn, leftTypeClosed);
            return {relationFn, std::move(head)};
        };

        // Normalize each written relation to its forward symbol: `≥`/`>`
        // flip to `≤`/`<` with `backward` set (their proofs are typed in
        // the normalized direction, `next R previous`); named relations
        // carry their operator symbol as written.
        auto normalizedSymbolOf = [](const SurfaceCalcStep& s)
                -> std::pair<std::string, bool> {
            if (!s.relationOperator.empty()) {
                return {s.relationOperator, false};
            }
            switch (s.relation) {
                case CalcRelation::LessOrEqual:    return {"≤", false};
                case CalcRelation::LessThan:       return {"<", false};
                case CalcRelation::GreaterOrEqual: return {"≤", true};
                case CalcRelation::GreaterThan:    return {"<", true};
                default:                           return {"=", false};
            }
        };

        // One elaborated step, carrying everything pass 2 composes on:
        // the proof, the resolved relation (its head builds transport
        // motives; its name owns the composition lemmas), and the
        // carrier its endpoints live at (per step — an `∈` hands the
        // chain from the element type to the set type).
        struct StepRecord {
            std::string symbol;   // normalized: "=", "≤", "<", "∣", …
            bool backward;        // written ≥/> (proof typed flipped)
            ExpressionPointer proof;
            std::string relationName;        // empty for "="
            ExpressionPointer relationHead;  // null for "="
            bool transitiveSwapped;  // bare-Natural ≤ transitivity quirk
            ExpressionPointer carrierType;
            LevelPointer carrierLevel;
            bool heterogeneous;   // `∈`: endpoints at different types
        };
        std::vector<StepRecord> steps;
        std::vector<ExpressionPointer> endpointKernels;
        endpointKernels.push_back(previousKernel);

        // PLAN_CALC_WIDENING §C — raise the running carrier. A step's
        // endpoint sits HIGHER in the coercion tower than everything
        // folded so far (e.g. a `d - 1 : Integer` endpoint in a chain
        // that started on Natural), so lift the recorded endpoints and
        // step proofs up `chain` — `=` by congruence of the coercion,
        // everything else by its `<edge>.<Slot>_preserves` lemma — and
        // continue the fold at the new carrier. Coercions only go up
        // the tower, so the carrier is a running maximum and nothing is
        // ever down-cast. The lifted endpoints stay in raw cast form
        // (not pushed to the leaves): that is exactly the form the
        // lifted proofs are typed at.
        auto raiseCarrier = [&](const std::vector<std::string>& chain,
                                ExpressionPointer newCarrierClosed) {
            for (const auto& record : steps) {
                if (record.heterogeneous) {
                    throwElaborate(
                        "this calc chain widens to a higher carrier after "
                        "a '" + record.symbol + "' step — a heterogeneous "
                        "step cannot be lifted along the coercion tower; "
                        "keep the chain at one carrier");
                }
            }
            for (size_t i = 0; i < steps.size(); ++i) {
                // A ≥/> step's proof is typed in the normalized forward
                // direction (next R previous); = and ≤/< proofs in the
                // user direction.
                ExpressionPointer lhs = steps[i].backward
                    ? endpointKernels[i + 1] : endpointKernels[i];
                ExpressionPointer rhs = steps[i].backward
                    ? endpointKernels[i] : endpointKernels[i + 1];
                steps[i].proof = liftRelationProofAcrossCoercions(
                    steps[i].proof, lhs, rhs, steps[i].symbol, chain,
                    localBinders);
            }
            for (auto& endpoint : endpointKernels) {
                endpoint = applyCoercionChain(endpoint, chain);
            }
            previousKernel = endpointKernels.back();
            carrierType = newCarrierClosed;
            carrierTypeName = headConstantName(newCarrierClosed);
            carrierLevel = typeUniverseOf(localBinders, previousKernel);
            // The relation lemma names were resolved at the old carrier;
            // clear them so they re-resolve lazily at the new one.
            leqRelationName.clear();
            transitiveTakesProofsSwapped = false;
            ltRelationName.clear();
            // Re-anchor every recorded step at the new carrier: its
            // endpoints were just lifted, so its relation head (and the
            // composition lemmas that hang off the relation name) must
            // re-resolve there. The preservation lemma that lifted the
            // proof concludes in the target carrier's registered
            // relation, so re-resolution names the relation the lifted
            // proof is already typed at.
            for (auto& record : steps) {
                record.carrierType = carrierType;
                record.carrierLevel = carrierLevel;
                if (record.symbol == "=") continue;
                if (record.symbol == "≤") {
                    resolveLeqNames();
                    record.relationName = leqRelationName;
                    record.relationHead = makeConstant(leqRelationName);
                    record.transitiveSwapped = transitiveTakesProofsSwapped;
                } else if (record.symbol == "<") {
                    resolveLtNames();
                    record.relationName = ltRelationName;
                    record.relationHead = makeConstant(ltRelationName);
                } else {
                    auto resolved = resolveNamedRelation(
                        record.symbol, carrierType, carrierTypeName);
                    record.relationName = resolved.first;
                    record.relationHead = resolved.second;
                }
            }
        };

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
            const auto [stepSymbol, stepBackward] = normalizedSymbolOf(step);
            const bool isEqualityStep = stepSymbol == "=";
            // Error messages speak the relation as WRITTEN (`≥`/`>`),
            // not its normalized forward form.
            const std::string stepDisplaySymbol = !stepBackward
                ? stepSymbol : (stepSymbol == "<" ? ">" : "≥");
            // `∈` is HETEROGENEOUS: its right endpoint (a set) lives at a
            // different type than the chain's carrier (the element type),
            // so it is elaborated bare and exempt from the carrier
            // reconciliation below; after the step the chain continues at
            // the set type.
            const bool heterogeneousStep = stepSymbol == "∈";
            ExpressionPointer nextKernel = elaborateExpression(
                *step.nextExpression, localBinders,
                heterogeneousStep ? nullptr : carrierType);
            // An endpoint whose type sits below the carrier in the
            // coercion tower (e.g. a bare Rational endpoint in a Real
            // calc) is lifted up to the carrier here. Passing carrierType
            // as the expected type does NOT itself trigger a tower
            // coercion — only ascriptions (dispatch.cpp) and operator
            // operands (combineOperands) do — so without this a bare
            // `… ≤ q` against a Real carrier would build a heterogeneous
            // relation and the endpoint would have to carry an explicit
            // `(q : Real)` ascription just to typecheck. Mirrors the
            // `=`-desugaring's mixed-type reconciliation, cast-normal form
            // included.
            if (!heterogeneousStep) {
                ExpressionPointer nextTypeRaw =
                    inferTypeInLocalContext(localBinders, nextKernel);
                std::string nextHead = headConstantName(nextTypeRaw);
                if (!nextHead.empty() && nextHead != carrierTypeName) {
                    ExpressionPointer nextTypeClosed = closeOverLocalBinders(
                        nextTypeRaw, localBinders, localBinders.size());
                    if (auto combined = combineOperands(
                            nextHead, carrierTypeName,
                            nextTypeClosed, carrierType)) {
                        if (!combined->coerceLeft.empty()) {
                            nextKernel = applyCoercionChain(
                                std::move(nextKernel), combined->coerceLeft);
                            nextKernel = castPushToLeaves(
                                nextKernel, localBinders).term;
                        }
                        if (!combined->coerceRight.empty()) {
                            // The endpoint's type is the join: the chain
                            // widens here (§C) — raise the carrier.
                            raiseCarrier(combined->coerceRight,
                                         combined->resultType);
                        }
                    }
                }
            }
            // Build the step's expected proof type from its relation.
            // For ≥/> the relation's arguments are flipped (a ≥ b is
            // proved as b ≤ a; a > b is proved as b < a).
            ExpressionPointer stepRelationType;
            std::string stepRelationName;
            ExpressionPointer stepRelationHead;
            bool stepSwapped = false;
            if (isEqualityStep) {
                stepRelationType = makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Equality", {carrierLevel}),
                            carrierType),
                        previousKernel),
                    nextKernel);
            } else if (stepSymbol == "≤" || stepSymbol == "<") {
                ExpressionPointer lhs =
                    stepBackward ? nextKernel : previousKernel;
                ExpressionPointer rhs =
                    stepBackward ? previousKernel : nextKernel;
                if (stepSymbol == "<") {
                    resolveLtNames();
                    stepRelationName = ltRelationName;
                } else {
                    resolveLeqNames();
                    stepRelationName = leqRelationName;
                    stepSwapped = transitiveTakesProofsSwapped;
                }
                stepRelationHead = makeConstant(stepRelationName);
                stepRelationType = makeApplication(
                    makeApplication(stepRelationHead, lhs), rhs);
            } else {
                // Named relation (`∣`, `⊆`, `≈`, `∈`): resolve at the
                // current carrier. The left operand is always at the
                // carrier; the right is too, except under `∈` (a Set).
                std::string rightHead = carrierTypeName;
                if (heterogeneousStep) {
                    rightHead = headConstantName(
                        inferTypeInLocalContext(localBinders, nextKernel));
                }
                auto resolved = resolveNamedRelation(
                    stepSymbol, carrierType, rightHead);
                stepRelationName = resolved.first;
                stepRelationHead = resolved.second;
                stepRelationType = makeApplication(
                    makeApplication(stepRelationHead, previousKernel),
                    nextKernel);
            }
            ExpressionPointer stepProofKernel;
            if (step.stepProof) {
                // Rewrite-under-Σ: a `Sum(r,f,n) = Sum(r,g,n)` step whose
                // `by` proof is the pointwise `(i) => f(i) = g(i)` desugars
                // to `Sum.extensional`. Tried first; nullptr unless both
                // endpoints are `Sum`s and the proof elaborates pointwise,
                // so it never shadows an ordinary step proof.
                if (isEqualityStep) {
                    stepProofKernel = tryUnderBinderStep(
                        localBinders, previousKernel, nextKernel,
                        *step.stepProof, step.line, step.column);
                }
                if (!stepProofKernel) {
                    stepProofKernel = elaborateExpression(
                        *step.stepProof, localBinders, stepRelationType);
                    if (std::getenv("MATH_DEBUG_CALC_STEP")) {
                        try {
                            std::cerr << "[calc-step] line " << step.line
                                << ": primary elaboration type: "
                                << prettyPrintForDisplay(
                                       inferTypeInLocalContext(
                                           localBinders, stepProofKernel))
                                << "\n";
                        } catch (...) {}
                    }
                    // `by (<fact>)`: when the proof position elaborates to a
                    // proposition P (its type is the `Proposition` sort) rather
                    // than a proof, the user cited a fact. Prove P and bridge
                    // its proof to the step exactly like `by <proof-of-P>`.
                    // Fact citations get the same redundancy probe as any
                    // other hint: removing the `by (P)` leaves exactly the
                    // bare step, which the probe below re-proves faithfully.
                    if (termIsProposition(localBinders, stepProofKernel)) {
                        stepProofKernel = bridgeCitedFact(
                            stepProofKernel, stepRelationType,
                            localBinders, step.line);
                    }
                    // B5 classifier (`MATH_CLASSIFY_HINTS`): record this
                    // hinted step's shape for the tier-sizing report. The
                    // `closes` bit re-proves by-less under the redundancy
                    // budget, faithfully per relation (the same split the
                    // redundancy check below uses); `unfolding` hints skip
                    // the probe (their transparency flip makes a
                    // speculative success spurious).
                    if (classifyHintsEnabled()) {
                        ExpressionPointer classifyAttempt;
                        if (std::get_if<SurfaceUnfold>(
                                &step.stepProof->node) == nullptr) {
                            uint64_t stepsBefore = kernelStepsSoFar();
                            RedundancyBudgetGuard budgetGuard(*this);
                            try {
                                // Faithful to the bare-step path for EVERY
                                // relation: a by-less `=` step also runs the
                                // full autoProveClaim (see the one-path note
                                // at the bare-equality branch below), so
                                // probing with the narrower autoProveCalcStep
                                // under-counted closes.
                                classifyAttempt = autoProveClaim(
                                    stepRelationType, localBinders,
                                    step.line);
                            } catch (const ElaborateError&) {
                                classifyAttempt = nullptr;
                            } catch (const TypeError&) {
                                classifyAttempt = nullptr;
                            } catch (const AutoProverBudgetError&) {
                                classifyAttempt = nullptr;
                            }
                            if (classifyAttempt
                                && redundancyReproofWasExpensive(
                                       stepsBefore)) {
                                classifyAttempt = nullptr;
                            }
                        }
                        std::string relationLabel =
                            stepSymbol == "≤" ? "<=" : stepSymbol;
                        emitHintClassification(
                            "calc", relationLabel.c_str(), stepRelationType,
                            step.stepProof.get(),
                            classifyAttempt != nullptr, step.line);
                    }
                    bool checkThisStep = reportRedundantBy_
                        && (isEqualityStep || reportRedundantByNonEq_);
                    if (checkThisStep) {
                        ExpressionPointer autoAttempt;
                        uint64_t stepsBefore = kernelStepsSoFar();
                        RedundancyBudgetGuard budgetGuard(*this);
                        try {
                            // Re-prove EXACTLY as a by-less step would at
                            // build time — the full autoProveClaim for every
                            // relation. A bare `=` step runs autoProveClaim
                            // too (the one-path note at the bare-equality
                            // branch below), so the narrower autoProveCalcStep
                            // this probe once used missed every hint whose
                            // bare close needs the later tactics (context-fact
                            // match, equality bridges, cast tiers). And only
                            // the faithful path measures the TRUE by-less
                            // cost, so the budget guard can leave a genuinely
                            // expensive re-proof unflagged (the hint earns
                            // its keep on speed). Non-`=` relations stay
                            // gated behind --check-redundant-by-non-eq; the
                            // budget caps the search so the check stays
                            // bounded.
                            autoAttempt = autoProveClaim(
                                stepRelationType, localBinders, step.line);
                        } catch (const ElaborateError&) {
                            autoAttempt = nullptr;
                        } catch (const TypeError&) {
                            autoAttempt = nullptr;
                        } catch (const AutoProverBudgetError&) {
                            // Budget tripped re-proving WITHOUT the hint:
                            // the hint is load-bearing (for speed at least).
                            // Never escapes — a speculative check must not
                            // fail the build.
                            autoAttempt = nullptr;
                        }
                        // A single deep conversion can close the by-less step
                        // while overshooting the low budget without tripping it
                        // (the budget is sampled only at candidate boundaries):
                        // measure the real cost and don't call an expensive
                        // re-proof "redundant".
                        if (autoAttempt
                            && redundancyReproofWasExpensive(stepsBefore)) {
                            autoAttempt = nullptr;
                        }
                        // The checker verifies its own suggestion (U3a): a
                        // real by-less step doesn't stop at autoProveClaim —
                        // it runs the final defeq gate between the produced
                        // proof's type and the step relation (the check at
                        // the end of the step loop). A probe proof that
                        // would fail that gate means the suggested edit
                        // breaks the build, so it is not "redundant".
                        if (autoAttempt) {
                            try {
                                ExpressionPointer probeType =
                                    inferTypeInLocalContext(
                                        localBinders, autoAttempt);
                                ExpressionPointer probeWanted =
                                    openOverLocalBinders(
                                        stepRelationType, localBinders,
                                        localBinders.size());
                                Context probeContext =
                                    buildContextFromLocalBinders(
                                        localBinders);
                                if (!isDefinitionallyEqual(
                                        environment_, probeContext,
                                        probeType, probeWanted)) {
                                    autoAttempt = nullptr;
                                }
                            } catch (...) {
                                autoAttempt = nullptr;
                            }
                        }
                        if (autoAttempt) {
                            std::cerr << "warning: " << moduleName_
                                << ":" << step.line << ":" << step.column
                                << ": redundant `by` on calc step — "
                                "auto-prover closes it without help\n";
                        } else {
                          if (isEqualityStep) {
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
                                            } catch (const AutoProverBudgetError&) {
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
                            const Declaration* citedDeclaration = head
                                ? environment_.lookup(head->qualifiedName)
                                : nullptr;
                            // Skip universe-POLYMORPHIC lemmas: the bare
                            // re-elaboration below (no universe args) forces the
                            // implicit-citation-level placeholder path, which
                            // corrupts elaborator state when its match fails.
                            // See the companion guard in elaborateStructuredClaim.
                            if (surfApp && !surfApp->arguments.empty()
                                && head && head->universeArgs.empty()
                                && head->qualifiedName != "congruenceOf"
                                && citedDeclaration
                                && universeParameterCount(*citedDeclaration)
                                       == 0) {
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
                                } catch (const AutoProverBudgetError&) {
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
                                                << " rel=" << stepSymbol
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
            } else if (isEqualityStep) {
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
                // Non-equality step (≤/</≥/>/named) without `by`.
                // Dispatch the step's relation type through the full
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
                        stepDisplaySymbol,
                        stepRelationType, localBinders);
                } catch (const ElaborateError&) {
                    stepProofKernel = nullptr;
                }
                if (!stepProofKernel) {
                    throwElaborate(
                        "I can't figure out why this calc "
                        + stepDisplaySymbol
                        + " step is true — the auto-prover couldn't close it "
                          "from context. Add `by <reason>`, or check that the "
                          "step actually holds."
                        + couldNotProveStepHint(previousKernel, nextKernel,
                              stepDisplaySymbol, stepRelationType,
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
                                        stepRelationTypeOpened,
                                        kDefeqProbeFuel)) {
                // Auto-rewrite fallback for = steps only.
                ExpressionPointer rewriteAttempt;
                if (step.stepProof
                    && isEqualityStep) {
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
                && isEqualityStep
                && !isDefinitionallyEqual(environment_, stepContext,
                                            stepProofType,
                                            stepRelationTypeOpened,
                                            kDefeqProbeFuel)) {
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
                && isEqualityStep
                && !isDefinitionallyEqual(environment_, stepContext,
                                            stepProofType,
                                            stepRelationTypeOpened,
                                            kDefeqProbeFuel)) {
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
            // Argument-free citation on a CONGRUENCE step: the cited lemma
            // matches a SUBTERM of the step, not the whole equality, so its
            // arguments can't be recovered by unifying against the goal — the
            // bare constant survives elaboration with its Pi type intact. Here
            // we descend the (previous, next) diff to the innermost differing
            // subterm, solve the lemma's arguments against that subterm, and
            // let the diff bridge wrap the result in the congruence. Lets the
            // user write `by add_negate_left` on `p + 0 = p + ((-p')+p')`
            // instead of spelling out `add_negate_left(ring, p')`.
            if (step.stepProof
                && isEqualityStep
                && std::holds_alternative<Pi>(stepProofType->node)
                && !isDefinitionallyEqual(environment_, stepContext,
                                            stepProofType,
                                            stepRelationTypeOpened,
                                            kDefeqProbeFuel)) {
                ExpressionPointer bareAttempt;
                try {
                    bareAttempt = tryApplyBareLemmaToDiff(
                        localBinders, previousKernel, nextKernel,
                        stepProofKernel, stepProofType,
                        step.line, step.column);
                } catch (const ElaborateError&) {
                    bareAttempt = nullptr;
                } catch (const TypeError&) {
                    bareAttempt = nullptr;
                }
                if (bareAttempt) {
                    try {
                        ExpressionPointer bareAttemptType =
                            inferTypeInLocalContext(localBinders,
                                bareAttempt);
                        if (isDefinitionallyEqual(environment_, stepContext,
                                                    bareAttemptType,
                                                    stepRelationTypeOpened)) {
                            stepProofKernel = bareAttempt;
                            stepProofType = bareAttemptType;
                        }
                    } catch (const TypeError&) {
                    } catch (const ElaborateError&) {
                    }
                }
            }
            // Argument-free citation whose CONCLUSION *is* the whole step
            // equality (not a congruence subterm): `= zero by
            // Ring.zero_multiply` on a step `multiply(zero, b) = zero`. The
            // bare lemma survives elaboration with its Pi type intact;
            // instantiate it goal-driven against the step's equality — the
            // same path `claim … by L` / `done by L` use — so an `=` step
            // can cite a lemma argument-free, exactly like a `≤` step or a
            // claim. (Complements the subterm-congruence case above, which
            // matches the lemma against a differing SUBTERM.)
            if (step.stepProof
                && isEqualityStep
                && std::holds_alternative<Pi>(stepProofType->node)
                && !isDefinitionallyEqual(environment_, stepContext,
                                            stepProofType,
                                            stepRelationTypeOpened,
                                            kDefeqProbeFuel)) {
                const bool debugCalcStep =
                    std::getenv("MATH_DEBUG_CALC_STEP") != nullptr;
                try {
                    ExpressionPointer filled = autoFillHintForClaim(
                        stepProofKernel, stepProofType, stepRelationType,
                        localBinders, step.line);
                    if (filled) {
                        ExpressionPointer filledType =
                            inferTypeInLocalContext(localBinders, filled);
                        if (isDefinitionallyEqual(environment_, stepContext,
                                                    filledType,
                                                    stepRelationTypeOpened)) {
                            stepProofKernel = filled;
                            stepProofType = filledType;
                        } else if (debugCalcStep) {
                            std::cerr << "[calc-step] line " << step.line
                                << ": whole-conclusion fill produced a "
                                "proof but its type failed the final "
                                "defeq:\n  filled: "
                                << prettyPrintForDisplay(filledType)
                                << "\n  wanted: "
                                << prettyPrintForDisplay(
                                       stepRelationTypeOpened) << "\n";
                        }
                    } else if (debugCalcStep) {
                        std::cerr << "[calc-step] line " << step.line
                            << ": whole-conclusion fill returned null\n";
                    }
                } catch (const ElaborateError& e) {
                    if (debugCalcStep) {
                        std::cerr << "[calc-step] line " << step.line
                            << ": whole-conclusion fill threw: "
                            << e.what() << "\n";
                    }
                } catch (const TypeError& e) {
                    if (debugCalcStep) {
                        std::cerr << "[calc-step] line " << step.line
                            << ": whole-conclusion fill TypeError: "
                            << e.what() << "\n";
                    }
                }
            }
            // Orientation retry. A citation whose conclusion has a bare
            // metavariable on one side — e.g. argument-free `by x + 0 = x`
            // on a REVERSED step `p = p + 0` — infers its arguments against
            // the goal and binds that side to the wrong endpoint, proving the
            // wrong equation. If the proof still doesn't match, re-elaborate
            // it against the SWAPPED step equality (which infers the
            // arguments correctly) and let the diff layer reapply the
            // symmetry. Only fires on an otherwise-failing equality step, and
            // only commits if the reoriented proof actually closes it — so it
            // can never turn a passing step into a wrong one.
            if (step.stepProof
                && isEqualityStep
                && !isDefinitionallyEqual(environment_, stepContext,
                                            stepProofType,
                                            stepRelationTypeOpened,
                                            kDefeqProbeFuel)) {
                ExpressionPointer swappedRelation;
                if (auto* appB = std::get_if<Application>(
                        &stepRelationType->node)) {
                    if (auto* appA = std::get_if<Application>(
                            &appB->function->node)) {
                        swappedRelation = makeApplication(
                            makeApplication(appA->function, appB->argument),
                            appA->argument);
                    }
                }
                if (swappedRelation) {
                    try {
                        ExpressionPointer altProof = elaborateExpression(
                            *step.stepProof, localBinders, swappedRelation);
                        ExpressionPointer altType =
                            inferTypeInLocalContext(localBinders, altProof);
                        ExpressionPointer diffAlt = tryDiffApplyUserProof(
                            localBinders, previousKernel, nextKernel,
                            altProof, altType, step.line, step.column);
                        if (diffAlt) {
                            ExpressionPointer diffAltType =
                                inferTypeInLocalContext(localBinders, diffAlt);
                            if (isDefinitionallyEqual(environment_,
                                    stepContext, diffAltType,
                                    stepRelationTypeOpened)) {
                                stepProofKernel = diffAlt;
                                stepProofType = diffAltType;
                            }
                        }
                    } catch (const ElaborateError&) {
                    } catch (const TypeError&) {
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
                std::string mismatchMessage =
                    "this step's justification proves a different relation "
                    "than the step claims\n"
                    "    this step claims:    "
                    + prettyPrintForDisplay(stepRelationTypeOpened) + "\n"
                    "    but its proof shows: "
                    + prettyPrintForDisplay(stepProofType);
                // When the step involves subtraction, a common cause is that
                // the two sides express it differently — `a - b` on one side,
                // `a + -b` on the other. These print ALIKE and are ring-equal,
                // but the structural matcher treats `subtract(a,b)` and
                // `add(a,-b)` as distinct, so a lemma stated one way won't
                // bridge a step written the other. The printed relations then
                // look bridgeable yet the step is rejected — hint at the real
                // obstacle.
                std::function<bool(const ExpressionPointer&)>
                    mentionsSubtractOrNegate =
                    [&](const ExpressionPointer& e) -> bool {
                        if (!e) return false;
                        if (auto* c = std::get_if<Constant>(&e->node)) {
                            const std::string& n = c->name;
                            auto endsWith = [&](const std::string& s) {
                                return n.size() >= s.size()
                                    && n.compare(n.size() - s.size(),
                                                 s.size(), s) == 0;
                            };
                            return endsWith("subtract") || endsWith("negate");
                        }
                        if (auto* a = std::get_if<Application>(&e->node))
                            return mentionsSubtractOrNegate(a->function)
                                || mentionsSubtractOrNegate(a->argument);
                        if (auto* p = std::get_if<Pi>(&e->node))
                            return mentionsSubtractOrNegate(p->domain)
                                || mentionsSubtractOrNegate(p->codomain);
                        if (auto* l = std::get_if<Lambda>(&e->node))
                            return mentionsSubtractOrNegate(l->domain)
                                || mentionsSubtractOrNegate(l->body);
                        return false;
                    };
                if (mentionsSubtractOrNegate(stepRelationTypeOpened)) {
                    mismatchMessage +=
                        "\n  note: this step involves subtraction — `a - b` and "
                        "`a + -b` print alike and are ring-equal, but the matcher "
                        "treats `subtract(a,b)` and `add(a,-b)` as DISTINCT, so a "
                        "lemma stated one way won't bridge a step written the "
                        "other. Write both sides the same way, or close the step "
                        "with `ring` (or a `by substituting` bridge).";
                }
                throwElaborate(mismatchMessage);
            }
            steps.push_back({stepSymbol, stepBackward, stepProofKernel,
                             stepRelationName, stepRelationHead, stepSwapped,
                             carrierType, carrierLevel, heterogeneousStep});
            endpointKernels.push_back(nextKernel);
            previousKernel = nextKernel;
            if (heterogeneousStep) {
                // `∈` hands the chain from the element type to the set
                // type: later `=` steps compare sets, so re-anchor the
                // carrier at the right endpoint's type.
                ExpressionPointer nextTypeOpen =
                    inferTypeInLocalContext(localBinders, nextKernel);
                carrierType = closeOverLocalBinders(
                    nextTypeOpen, localBinders, localBinders.size());
                carrierTypeName = headConstantName(nextTypeOpen);
                carrierLevel = typeUniverseOf(localBinders, nextKernel);
                leqRelationName.clear();
                transitiveTakesProofsSwapped = false;
                ltRelationName.clear();
            }
        }

        // Optional check: look for redundant intermediate calc steps.
        // For each internal endpoint (not the first or last), see whether the
        // auto-prover can close the combined step directly. If yes, warn — the
        // user can usually delete the intermediate `= midpoint` line without
        // losing kernel acceptance. Restricted to all-`=` runs (mixed
        // `=`/`≤`/`<` combinations need per-case relation arithmetic). Off by
        // default — the auto-prover dispatch is expensive on long chains.
        //
        // The walk is CUMULATIVE (greedy): `lastKept` is the most recent
        // endpoint we decided to KEEP, and each candidate is tested against the
        // combined step FROM `lastKept` — i.e. as if every midpoint flagged so
        // far in this run were already removed. So a run of midpoints is only
        // extended while the growing combined step still closes under the
        // redundancy budget; the moment it would tip over, the run ends and the
        // current endpoint is kept. This means deleting ALL flagged midpoints at
        // once is safe by construction (each maximal run collapses to a single
        // step the auto-prover closes within budget) — it can't suggest a set
        // of removals that compound into an expensive search.
        if (reportRedundantCalcSteps_) {
            size_t lastKept = 0;
            for (size_t k = 1; k + 1 <= steps.size(); ++k) {
                // The combined step, if endpoint k is removed together with
                // every midpoint already flagged in this run, is
                // endpointKernels[lastKept] = endpointKernels[k+1]. It is a
                // genuine `=` step only when every step in the span
                // [lastKept, k] is Equality.
                bool spanAllEquality = true;
                for (size_t j = lastKept; j <= k; ++j) {
                    if (steps[j].symbol != "=") {
                        spanAllEquality = false;
                        break;
                    }
                }
                if (!spanAllEquality) {
                    lastKept = k;
                    continue;
                }
                // The span's own carrier, not the chain-final one: an `∈`
                // later in the chain moves the carrier to the set type,
                // but this all-`=` span's endpoints live where they were
                // recorded.
                ExpressionPointer combinedRelation = makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Equality",
                                {steps[lastKept].carrierLevel}),
                            steps[lastKept].carrierType),
                        endpointKernels[lastKept]),
                    endpointKernels[k + 1]);
                // Measure with the SAME prover a by-less `=` step verifies
                // through — `autoProveClaim` (equality battery, then the full
                // tactic set). Using the narrower `autoProveCalcStep` here
                // under-measured: it could close the combined step cheaply
                // while the actual by-less re-proof takes the full tactic
                // set's pricier path, so a "cheap" suggestion turned into an
                // expensive search once the midpoint was deleted. Closing over
                // the local binders to match autoProveClaim's goal contract.
                ExpressionPointer combinedRelationClosed = closeOverLocalBinders(
                    combinedRelation, localBinders, localBinders.size());
                ExpressionPointer autoAttempt;
                {
                    // Cap the budget so collapsing is only suggested when the
                    // combined step stays cheap (a costly re-proof means the
                    // intermediate is pulling its weight).
                    uint64_t stepsBefore = kernelStepsSoFar();
                    RedundancyBudgetGuard budgetGuard(*this);
                    try {
                        autoAttempt = autoProveClaim(
                            combinedRelationClosed, localBinders,
                            calc.steps[k - 1].line);
                    } catch (const AutoProverBudgetError&) {
                        autoAttempt = nullptr;
                    } catch (const ElaborateError&) {
                        autoAttempt = nullptr;
                    } catch (const TypeError&) {
                        autoAttempt = nullptr;
                    }
                    // A single deep conversion can close the combined step
                    // while overshooting the low budget without tripping it;
                    // keep the intermediate target when the collapse is
                    // actually expensive.
                    if (autoAttempt
                        && redundancyReproofWasExpensive(stepsBefore)) {
                        autoAttempt = nullptr;
                    }
                }
                if (autoAttempt) {
                    // Endpoint k is removable (collapsing the run [lastKept,
                    // k+1] into one step). It is the target of steps[k-1] and is
                    // written on that step's line. Keep `lastKept` where it is
                    // so the next candidate is tested against the still-growing
                    // combined step.
                    std::cerr << "warning: " << moduleName_
                        << ":" << calc.steps[k - 1].line
                        << ":" << calc.steps[k - 1].column
                        << ": calc intermediate target at this line is "
                        "redundant — removing it lets the auto-prover "
                        "close the combined step (next endpoint at line "
                        << calc.steps[k].line << ")\n";
                } else {
                    // The combined step would be too expensive: this endpoint
                    // pulls its weight, so keep it and start a fresh run here.
                    lastKept = k;
                }
            }
        }

        // Direction check: a chain may not mix forward non-`=` steps
        // (<, ≤, and the named relations) with backward ones (>, ≥).
        bool chainHasForward = false;
        bool chainHasBackward = false;
        for (const auto& s : steps) {
            if (s.symbol == "=") continue;
            if (s.backward) chainHasBackward = true;
            else chainHasForward = true;
        }
        if (chainHasForward && chainHasBackward) {
            throwElaborate(
                "calc chain mixes forward (<, ≤) and backward "
                "(>, ≥) inequalities — only = is allowed in "
                "either direction");
        }

        // Normalize for backward chains: reverse endpoint and step
        // order. Each backward ≥/> step's proof already has type
        // matching the normalized direction (a ≥ b's proof is b ≤ a,
        // exactly what the reversed walk wants going from b to a).
        // But a backward chain's `=` steps were elaborated with type
        // `previous = next` (user-direction); the normalized walk
        // needs `next = previous`, so we flip them via
        // Equality.symmetry.
        std::vector<ExpressionPointer> normalizedEndpoints =
            endpointKernels;
        std::vector<StepRecord> normalizedSteps = steps;
        if (chainHasBackward) {
            std::reverse(normalizedEndpoints.begin(),
                          normalizedEndpoints.end());
            std::reverse(normalizedSteps.begin(),
                          normalizedSteps.end());
            for (size_t k = 0; k < normalizedSteps.size(); ++k) {
                if (normalizedSteps[k].symbol != "=") continue;
                // normalizedSteps[k] corresponds to user's step
                // (N-1-k), whose endpoints are
                // (endpointKernels[N-1-k], endpointKernels[N-k]) =
                // (normalizedEndpoints[k+1], normalizedEndpoints[k]).
                // Build symmetry over the user-direction endpoints.
                ExpressionPointer call = makeConstant(
                    "Equality.symmetry",
                    {normalizedSteps[k].carrierLevel});
                call = makeApplication(std::move(call),
                    normalizedSteps[k].carrierType);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k + 1]);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k]);
                call = makeApplication(std::move(call),
                    normalizedSteps[k].proof);
                normalizedSteps[k].proof = std::move(call);
            }
        }

        // A single step IS the chain, whatever its relation.
        if (normalizedSteps.size() == 1) {
            return normalizedSteps[0].proof;
        }

        // PLAN_CALC_WIDENING §D — the relation-composition registry.
        // The accumulator proves `left R mid`; each step `mid R′ next`
        // folds in by one of:
        //   * `=` · `=`  — `Equality.transitivity`;
        //   * R · `=`    — transport the accumulator's right endpoint
        //                  along the step equality (works for every R);
        //   * `=` · R′   — transport the step's left endpoint back along
        //                  the accumulated equality (works for every R′);
        //   * R · R′     — a composition rule: a same-relation pair
        //                  defaults to the relation's own transitivity
        //                  lemma (`<R>.transitive`, or `<R>_transitive` —
        //                  any relation gains calc support by declaring
        //                  one); the table rows below are the genuinely
        //                  mixed pairs (the ≤/< strictness arithmetic).
        //                  A pair matching no rule is a legible error.
        struct CompositionRule {
            const char* leftSymbol;
            const char* rightSymbol;
            bool lemmaFromRight;    // which side's relation owns the
                                    // lemma — and the result relation
            const char* lemmaSuffix;
            bool weakenLeftFirst;   // < · <: weaken the accumulated
                                    // strict proof to ≤ first
        };
        static const CompositionRule compositionRules[] = {
            {"≤", "<", /*lemmaFromRight=*/true,  ".transitive_left",  false},
            {"<", "≤", /*lemmaFromRight=*/false, ".transitive_right", false},
            {"<", "<", /*lemmaFromRight=*/false, ".transitive_left",  true},
        };

        StepRecord running = normalizedSteps[0];
        ExpressionPointer left = normalizedEndpoints[0];
        for (size_t k = 1; k < normalizedSteps.size(); ++k) {
            const StepRecord& stepRecord = normalizedSteps[k];
            ExpressionPointer mid = normalizedEndpoints[k];
            ExpressionPointer next = normalizedEndpoints[k + 1];
            if (running.symbol == "=" && stepRecord.symbol == "=") {
                ExpressionPointer call = makeConstant(
                    "Equality.transitivity", {stepRecord.carrierLevel});
                for (ExpressionPointer a : {stepRecord.carrierType, left,
                                             mid, next, running.proof,
                                             stepRecord.proof}) {
                    call = makeApplication(std::move(call), a);
                }
                running.proof = std::move(call);
            } else if (stepRecord.symbol == "=") {
                // R · = : transport the accumulator's right endpoint,
                // R(left, mid) → R(left, next). The motive's captured
                // terms shift up by one under the new binder.
                ExpressionPointer motive = makeLambda(
                    "z", stepRecord.carrierType,
                    makeApplication(
                        makeApplication(shift(running.relationHead, 1),
                                        shift(left, 1)),
                        makeBoundVariable(0)));
                ExpressionPointer call = makeConstant(
                    "Equality.transport_proposition",
                    {stepRecord.carrierLevel});
                for (ExpressionPointer a : {stepRecord.carrierType, motive,
                                             mid, next, stepRecord.proof,
                                             running.proof}) {
                    call = makeApplication(std::move(call), a);
                }
                running.proof = std::move(call);
            } else if (running.symbol == "=") {
                // = · R′ : transport the step's left endpoint backwards,
                // R′(mid, next) → R′(left, next); the accumulator adopts
                // the step's relation.
                ExpressionPointer symmetry = makeConstant(
                    "Equality.symmetry", {running.carrierLevel});
                for (ExpressionPointer a : {running.carrierType, left, mid,
                                             running.proof}) {
                    symmetry = makeApplication(std::move(symmetry), a);
                }
                ExpressionPointer motive = makeLambda(
                    "z", running.carrierType,
                    makeApplication(
                        makeApplication(shift(stepRecord.relationHead, 1),
                                        makeBoundVariable(0)),
                        shift(next, 1)));
                ExpressionPointer call = makeConstant(
                    "Equality.transport_proposition",
                    {running.carrierLevel});
                for (ExpressionPointer a : {running.carrierType, motive,
                                             mid, left, symmetry,
                                             stepRecord.proof}) {
                    call = makeApplication(std::move(call), a);
                }
                ExpressionPointer composed = std::move(call);
                running = stepRecord;
                running.proof = std::move(composed);
            } else {
                // R · R′ : consult the composition registry.
                const CompositionRule* rule = nullptr;
                for (const auto& candidate : compositionRules) {
                    if (running.symbol == candidate.leftSymbol
                        && stepRecord.symbol == candidate.rightSymbol) {
                        rule = &candidate;
                        break;
                    }
                }
                static const CompositionRule sameSymbolRule =
                    {"", "", /*lemmaFromRight=*/false, ".transitive",
                     false};
                if (!rule && running.symbol == stepRecord.symbol) {
                    rule = &sameSymbolRule;
                }
                if (!rule) {
                    throwElaborate(
                        "nothing composes a '" + running.symbol
                        + "' step with a following '" + stepRecord.symbol
                        + "' step in a calc chain — `=` composes with "
                        "every relation; any other pair needs a "
                        "relation-composition rule");
                }
                const StepRecord& owner =
                    rule->lemmaFromRight ? stepRecord : running;
                std::string lemmaName =
                    owner.relationName + rule->lemmaSuffix;
                bool isPlainTransitive =
                    std::string(rule->lemmaSuffix) == ".transitive";
                if (isPlainTransitive
                    && environment_.lookup(lemmaName) == nullptr
                    && environment_.lookup(
                           owner.relationName + "_transitive")) {
                    // The `<R>_transitive` naming convention (e.g.
                    // Natural.divides_transitive).
                    lemmaName = owner.relationName + "_transitive";
                }
                if (environment_.lookup(lemmaName) == nullptr) {
                    throwElaborate(
                        "calc composes '" + running.symbol + "' with '"
                        + stepRecord.symbol + "' via `" + lemmaName + "`"
                        + (isPlainTransitive
                               ? " (or `" + owner.relationName
                                 + "_transitive`)"
                               : std::string())
                        + ", which is not in scope");
                }
                ExpressionPointer firstProof = running.proof;
                if (rule->weakenLeftFirst) {
                    ExpressionPointer weaken = makeConstant(
                        owner.relationName + ".weaken");
                    for (ExpressionPointer a : {left, mid, firstProof}) {
                        weaken = makeApplication(std::move(weaken), a);
                    }
                    firstProof = std::move(weaken);
                }
                // The lemma's leading implicits (e.g. the `{T}` of
                // `Set.subset.transitive`) are recovered from the
                // endpoint type, exactly like an operator call's.
                ExpressionPointer call = applyOperatorImplicitFillers(
                    makeConstant(lemmaName), lemmaName, owner.carrierType);
                for (ExpressionPointer a : {left, mid, next}) {
                    call = makeApplication(std::move(call), a);
                }
                // The bare-Natural `LessOrEqual.transitive` takes its
                // proofs in (b≤c, a≤b) order — a historical accident
                // flagged at resolution.
                bool swapProofs =
                    owner.transitiveSwapped && isPlainTransitive;
                ExpressionPointer secondProof = stepRecord.proof;
                if (swapProofs) {
                    call = makeApplication(std::move(call),
                                            std::move(secondProof));
                    call = makeApplication(std::move(call),
                                            std::move(firstProof));
                } else {
                    call = makeApplication(std::move(call),
                                            std::move(firstProof));
                    call = makeApplication(std::move(call),
                                            std::move(secondProof));
                }
                ExpressionPointer composed = std::move(call);
                running = owner;
                running.proof = std::move(composed);
            }
        }
        return running.proof;
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
        registerSignJudgmentRule(theoremName, typeExpr);
        registerMonotonicityRule(theoremName, typeExpr);
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
        RewriteLemma reverseEntry;
        reverseEntry.lemmaName = theoremName;
        reverseEntry.binderCount = binderCount;
        reverseEntry.lhs = lhs;
        reverseEntry.rhs = rhs;
        reverseEntry.binderTypes = std::move(binderTypes);
        reverseEntry.reverseDirection = true;
        // Dual-key each side. When a side's spine head is a notation wrapper
        // (`length`'s `List.lengthOf`, `∖`'s `List.removeFrom`), also file the
        // entry under its raw head's bucket (`List.length` / `List.remove`),
        // so a raw-form goal reaches this wrapper-form lemma. The stored
        // pattern stays as written — matchAgainstPattern bridges the head.
        uint64_t lhsKey = spineHash(lhs);
        uint64_t rhsKey = spineHash(rhs);
        std::optional<uint64_t> lhsRawKey = rawKeyForSpineKey(lhsKey);
        std::optional<uint64_t> rhsRawKey = rawKeyForSpineKey(rhsKey);
        if (lhsRawKey) lemmaIndex_.emplace(*lhsRawKey, forwardEntry);
        if (rhsRawKey) lemmaIndex_.emplace(*rhsRawKey, reverseEntry);
        lemmaIndex_.emplace(lhsKey, std::move(forwardEntry));
        lemmaIndex_.emplace(rhsKey, std::move(reverseEntry));
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
        bool endpointsDefinitionallyEqual = false;
        try {
            endpointsDefinitionallyEqual = isDefinitionallyEqual(
                environment_, openedContext, previousOpened, nextOpened);
        } catch (const TypeError&) {
            // The defeq recursion re-types subterms it manufactures
            // mid-unfold (proof irrelevance), and across the soft-opaque
            // quotient-alias boundary that inference can fail on a term
            // neither side wrote. This probe is SPECULATIVE — treat the
            // mishap as "not equal by this strategy" and let the later
            // strategies (or the step's own loud failure) speak.
            endpointsDefinitionallyEqual = false;
        }
        if (endpointsDefinitionallyEqual) {
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
            // B3.1: cast-equality tier — leaf-normalize both endpoints,
            // lower a same-hop `ι(a) = ι(b)` to the source carrier and
            // re-run the battery there (lifting by congruence), or retry
            // once at the normalized endpoints.
            ExpressionPointer castProof = tryCastEqualityTier(
                localBinders, previousKernel, nextKernel,
                carrierType, carrierLevel, stepEqualityType,
                line, column);
            if (castProof) return castProof;
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


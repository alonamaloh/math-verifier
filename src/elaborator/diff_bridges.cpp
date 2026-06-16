// Out-of-line Elaborator method definitions: diff-based proof bridges (under-binder, cited+context, user-proof, AC) + pattern match
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::tryDiffWrapForEqualityGoal(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer hintTerm,
        ExpressionPointer hintType,
        ExpressionPointer goalClosed) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        ExpressionPointer goalWhnf = weakHeadNormalForm(
            environment_, goalOpened);
        EqualityComponents goalComps;
        try {
            goalComps = extractEqualityComponents(
                goalWhnf, "diff-wrap goal", 0);
        } catch (const ElaborateError&) {
            return nullptr;
        }
        ExpressionPointer previousKernel = closeOverLocalBinders(
            goalComps.leftEndpoint, localBinders,
            localBinders.size());
        ExpressionPointer nextKernel = closeOverLocalBinders(
            goalComps.rightEndpoint, localBinders,
            localBinders.size());
        try {
            return tryDiffApplyUserProof(
                localBinders, previousKernel, nextKernel,
                hintTerm, hintType, 0, 0);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
    }

bool Elaborator::isPointwiseEqualityType(ExpressionPointer type) {
        ExpressionPointer cursor = weakHeadNormalForm(environment_, type);
        while (auto* pi = std::get_if<Pi>(&cursor->node)) {
            cursor = weakHeadNormalForm(environment_, pi->codomain);
        }
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            cursor = application->function;
        }
        auto* head = std::get_if<Constant>(&cursor->node);
        return head && head->name == "Equality";
    }

ExpressionPointer Elaborator::tryUnderBinderStep(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previous, ExpressionPointer next,
        const SurfaceExpression& proofSurface, int line, int column) {
        (void)line; (void)column;
        // Only fire when the `by` proof is syntactically a lambda — the
        // under-binder form IS `function (i) => <pointwise proof>`. An
        // ordinary lemma proof is left to the normal path.
        if (!std::get_if<SurfaceLambda>(&proofSurface.node)) {
            return nullptr;
        }
        // Peel `Head(arg0, …, argN)` → (head name, args outermost-first).
        auto peelApplication = [&](ExpressionPointer expression,
                                   std::vector<ExpressionPointer>& args)
                -> std::string {
            ExpressionPointer cursor = expression;
            while (auto* application =
                       std::get_if<Application>(&cursor->node)) {
                args.push_back(application->argument);
                cursor = application->function;
            }
            std::reverse(args.begin(), args.end());
            auto* head = std::get_if<Constant>(&cursor->node);
            return head ? head->name : std::string();
        };
        std::vector<ExpressionPointer> argsLeft, argsRight;
        std::string headLeft = peelApplication(previous, argsLeft);
        std::string headRight = peelApplication(next, argsRight);
        if (headLeft.empty() || headLeft != headRight) return nullptr;
        if (argsLeft.size() != argsRight.size() || argsLeft.empty()) {
            return nullptr;
        }
        // Exactly one differing argument position, and both sides there are
        // lambdas (the binder body).
        int diffPosition = -1;
        for (size_t i = 0; i < argsLeft.size(); ++i) {
            if (!structurallyEqual(argsLeft[i], argsRight[i])) {
                if (diffPosition >= 0) return nullptr;  // more than one diff
                diffPosition = static_cast<int>(i);
            }
        }
        if (diffPosition < 0) return nullptr;  // identical (reflexivity)
        // The differing argument is the binder body (`f` vs `g`) — it need
        // not be a literal lambda (an abstract function variable is fine);
        // the lemma lookup + pointwise elaboration + final type-check below
        // reject anything that isn't genuinely a congruence-under-binder.
        ExpressionPointer summandF = argsLeft[diffPosition];
        ExpressionPointer summandG = argsRight[diffPosition];

        // Try each congruence lemma registered for this function head via
        // `congruence_under_binder <F> := <L>;`.
        auto registryEntry =
            environment_.congruenceUnderBinderRegistry.find(headLeft);
        if (registryEntry == environment_.congruenceUnderBinderRegistry.end()) {
            return nullptr;
        }
        for (const std::string& lemmaName : registryEntry->second) {
            if (!environment_.lookup(lemmaName)) continue;
            try {
                // Apply to: shared prefix (args before the binder) + f + g.
                ExpressionPointer partial = makeConstant(lemmaName);
                for (int i = 0; i < diffPosition; ++i) {
                    partial = makeApplication(std::move(partial), argsLeft[i]);
                }
                partial = makeApplication(std::move(partial), summandF);
                partial = makeApplication(std::move(partial), summandG);
                // Fill remaining binders: the user's lambda for the unique
                // pointwise-equality binder, shared suffix args for the rest.
                size_t suffixIndex = static_cast<size_t>(diffPosition) + 1;
                bool lambdaUsed = false;
                for (int guard = 0; guard < 16; ++guard) {
                    ExpressionPointer partialType = weakHeadNormalForm(
                        environment_,
                        inferTypeInLocalContext(localBinders, partial));
                    auto* pi = std::get_if<Pi>(&partialType->node);
                    if (!pi) break;  // fully applied
                    if (!lambdaUsed
                        && isPointwiseEqualityType(pi->domain)) {
                        ExpressionPointer expected = closeOverLocalBinders(
                            pi->domain, localBinders, localBinders.size());
                        ExpressionPointer proof = elaborateExpression(
                            proofSurface, localBinders, expected);
                        partial = makeApplication(std::move(partial), proof);
                        lambdaUsed = true;
                    } else if (suffixIndex < argsLeft.size()) {
                        partial = makeApplication(std::move(partial),
                                                   argsLeft[suffixIndex++]);
                    } else {
                        break;  // cannot fill
                    }
                }
                if (!lambdaUsed) continue;
                // Validate: a fully-applied, well-typed proof.
                ExpressionPointer resultType =
                    inferTypeInLocalContext(localBinders, partial);
                if (std::get_if<Pi>(&weakHeadNormalForm(
                        environment_, resultType)->node)) {
                    continue;  // still under-applied
                }
                return partial;
            } catch (const ElaborateError&) {
                continue;
            } catch (const TypeError&) {
                continue;
            }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryCombineCitedWithContext(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer userProof,
        ExpressionPointer userLeft,
        ExpressionPointer userRight,
        ExpressionPointer userCarrier,
        LevelPointer userCarrierLevel,
        int line, int column) {
        if (environment_.lookup("Equality.congruence") == nullptr
            || environment_.lookup("Equality.transitivity") == nullptr) {
            return nullptr;
        }
        auto carrierTypeOf = [&](const ExpressionPointer& expr) {
            return closeOverLocalBinders(
                inferTypeInLocalContext(localBinders, expr),
                localBinders, localBinders.size());
        };
        // The cited proof oriented `from = to`. `forward` uses it as-is
        // (from = userLeft); otherwise wrap with `Equality.symmetry`
        // (from = userRight).
        auto orientedProof = [&](bool forward) -> ExpressionPointer {
            if (forward) return userProof;
            ExpressionPointer sym = makeConstant(
                "Equality.symmetry", {userCarrierLevel});
            sym = makeApplication(std::move(sym), userCarrier);
            sym = makeApplication(std::move(sym), userLeft);
            sym = makeApplication(std::move(sym), userRight);
            sym = makeApplication(std::move(sym), userProof);
            return sym;
        };
        // Flip a proof `proof : x = y` into `y = x` at the endpoint type.
        auto symmetrize = [&](const ExpressionPointer& x,
                              const ExpressionPointer& y,
                              ExpressionPointer proof) -> ExpressionPointer {
            LevelPointer level = typeUniverseOf(localBinders, x);
            ExpressionPointer s = makeConstant(
                "Equality.symmetry", {level});
            s = makeApplication(std::move(s), carrierTypeOf(x));
            s = makeApplication(std::move(s), x);
            s = makeApplication(std::move(s), y);
            s = makeApplication(std::move(s), std::move(proof));
            return s;
        };
        // Rewrite `endpoint` by congruence: abstract every occurrence of
        // `from`, substitute `to`, and wrap with `Equality.congruence`.
        // Returns {proof : endpoint = rewritten, rewritten} or {nullptr,
        // nullptr} if `from` does not occur.
        struct Rewritten {
            ExpressionPointer proof;
            ExpressionPointer result;
        };
        auto rewriteEndpoint =
            [&](const ExpressionPointer& endpoint,
                const ExpressionPointer& from, const ExpressionPointer& to,
                ExpressionPointer citedProof) -> Rewritten {
            int occurrences = 0;
            ExpressionPointer motiveBody = abstractStructuralOccurrence(
                endpoint, from, 0, occurrences);
            if (occurrences == 0) return {nullptr, nullptr};
            ExpressionPointer rewritten = substitute(motiveBody, 0, to);
            try {
                ExpressionPointer outerType = carrierTypeOf(endpoint);
                LevelPointer outerLevel = typeUniverseOf(
                    localBinders, endpoint);
                ExpressionPointer motive = makeLambda(
                    "_combine_z", userCarrier, std::move(motiveBody));
                ExpressionPointer call = makeConstant(
                    "Equality.congruence", {userCarrierLevel, outerLevel});
                call = makeApplication(std::move(call), userCarrier);
                call = makeApplication(std::move(call), std::move(outerType));
                call = makeApplication(std::move(call), std::move(motive));
                call = makeApplication(std::move(call), from);
                call = makeApplication(std::move(call), to);
                call = makeApplication(std::move(call), std::move(citedProof));
                return {std::move(call), std::move(rewritten)};
            } catch (const TypeError&) {
                return {nullptr, nullptr};
            } catch (const ElaborateError&) {
                return {nullptr, nullptr};
            }
        };
        // Join `prev = mid` (p) and `mid = next` (q) by transitivity.
        auto transitivityJoin =
            [&](const ExpressionPointer& prev, const ExpressionPointer& mid,
                const ExpressionPointer& next, ExpressionPointer p,
                ExpressionPointer q) -> ExpressionPointer {
            try {
                LevelPointer level = typeUniverseOf(localBinders, prev);
                ExpressionPointer trans = makeConstant(
                    "Equality.transitivity", {level});
                trans = makeApplication(std::move(trans), carrierTypeOf(prev));
                trans = makeApplication(std::move(trans), prev);
                trans = makeApplication(std::move(trans), mid);
                trans = makeApplication(std::move(trans), next);
                trans = makeApplication(std::move(trans), std::move(p));
                trans = makeApplication(std::move(trans), std::move(q));
                return trans;
            } catch (const TypeError&) {
                return nullptr;
            } catch (const ElaborateError&) {
                return nullptr;
            }
        };
        auto eqType = [&](const ExpressionPointer& x,
                          const ExpressionPointer& y) {
            LevelPointer level = typeUniverseOf(localBinders, x);
            ExpressionPointer e = makeConstant("Equality", {level});
            e = makeApplication(std::move(e), carrierTypeOf(x));
            e = makeApplication(std::move(e), x);
            e = makeApplication(std::move(e), y);
            return e;
        };
        auto closeResidual =
            [&](const ExpressionPointer& a,
                const ExpressionPointer& b) -> ExpressionPointer {
            return autoProveCalcStep(
                localBinders, a, b, carrierTypeOf(a),
                typeUniverseOf(localBinders, a), eqType(a, b), line, column);
        };
        // Four attempts: rewrite the PREVIOUS endpoint (then auto-prove
        // `mid = next`) or the NEXT endpoint (auto-prove `prev = mid`),
        // each rewriting in the forward (userLeft → userRight) or flipped
        // direction. First residual the auto-prover closes from context wins.
        struct Attempt { bool onPrevious; bool forward; };
        const Attempt attempts[] = {
            {true, true}, {true, false}, {false, true}, {false, false}};
        for (const Attempt& attempt : attempts) {
            const ExpressionPointer& from =
                attempt.forward ? userLeft : userRight;
            const ExpressionPointer& to =
                attempt.forward ? userRight : userLeft;
            if (attempt.onPrevious) {
                Rewritten rw = rewriteEndpoint(
                    previousKernel, from, to, orientedProof(attempt.forward));
                if (!rw.proof) continue;
                ExpressionPointer residual =
                    closeResidual(rw.result, nextKernel);
                if (!residual) continue;
                ExpressionPointer joined = transitivityJoin(
                    previousKernel, rw.result, nextKernel,
                    std::move(rw.proof), std::move(residual));
                if (joined && !containsFreeVariable(joined)) return joined;
            } else {
                Rewritten rw = rewriteEndpoint(
                    nextKernel, from, to, orientedProof(attempt.forward));
                if (!rw.proof) continue;
                // rw.proof : nextKernel = mid; flip to mid = nextKernel.
                ExpressionPointer midToNext =
                    symmetrize(nextKernel, rw.result, std::move(rw.proof));
                ExpressionPointer residual =
                    closeResidual(previousKernel, rw.result);
                if (!residual) continue;
                ExpressionPointer joined = transitivityJoin(
                    previousKernel, rw.result, nextKernel,
                    std::move(residual), std::move(midToNext));
                if (joined && !containsFreeVariable(joined)) return joined;
            }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryDiffApplyUserProof(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer userProof,
        ExpressionPointer userProofType,
        int line, int column) {
        (void)column;
        (void)line;
        // The diff-inference fallback wraps with Equality.congruence;
        // refuse the attempt if that name isn't declared, otherwise we'd
        // hand the kernel a term referencing an undefined constant and
        // the eventual addDefinition would report it without any calc-
        // step attribution context (the calc-step frame is long gone by
        // then). Returning nullptr here lets the caller fall through to
        // its normal "type mismatch" error path, which fires inside the
        // calc-step Frame and reports the line of the offending step.
        if (!environment_.lookup("Equality.congruence")) {
            return nullptr;
        }
        // Extract (carrierLevel, T, a, b) from userProofType.
        ExpressionPointer userTypeWhnf = weakHeadNormalForm(
            environment_, userProofType);
        EqualityComponents components;
        try {
            components = extractEqualityComponents(
                userTypeWhnf, "calc step diff", line);
        } catch (const ElaborateError&) {
            return nullptr;
        }
        ExpressionPointer userLeft = components.leftEndpoint;
        ExpressionPointer userRight = components.rightEndpoint;
        ExpressionPointer userCarrier = components.carrierType;
        LevelPointer userCarrierLevel = components.carrierUniverseLevel;
        // Representation contract (WS5/WS8). This helper has two callers that
        // pass `userProofType` in DIFFERENT representations: the theorem-body
        // coercion path passes it CLOSED over the local binders (de Bruijn
        // indices), while the calc-step path passes it OPENED (the binders as
        // named Internal FreeVariables). The symmetric-flip branch below
        // builds `Equality.symmetry(carrier, x, y, proof)` directly from these
        // endpoints — correct only when they are CLOSED, else the opened
        // `@a`/`@e` free variables leak into the proof term and it is rejected
        // as malformed (the calc-step case that kept its explicit symmetry).
        // Normalize to CLOSED here so both callers behave identically; the
        // `openOverLocalBinders` comparisons below re-open as needed.
        auto closeIfOpened = [&](const ExpressionPointer& e) {
            return containsFreeVariable(e)
                ? closeOverLocalBinders(e, localBinders, localBinders.size())
                : e;
        };
        userLeft = closeIfOpened(userLeft);
        userRight = closeIfOpened(userRight);
        userCarrier = closeIfOpened(userCarrier);
        // ζ-unfold local let-binders (consistent with autoProveCalcStep).
        previousKernel = zetaUnfoldLetBinders(previousKernel, localBinders);
        nextKernel = zetaUnfoldLetBinders(nextKernel, localBinders);
        Context openedContext = buildContextFromLocalBinders(localBinders);
        // Lockstep walk: descend via App nodes, at each level check
        // if the user proof matches (forward or symmetric).
        std::vector<CalcCongruencePathStep> pathStepsOutsideIn;
        ExpressionPointer leftCursor = previousKernel;
        ExpressionPointer rightCursor = nextKernel;
        ExpressionPointer innerProof = nullptr;
        ExpressionPointer userLeftOpened = openOverLocalBinders(
            userLeft, localBinders, localBinders.size());
        ExpressionPointer userRightOpened = openOverLocalBinders(
            userRight, localBinders, localBinders.size());
        while (true) {
            ExpressionPointer leftOpened = openOverLocalBinders(
                leftCursor, localBinders, localBinders.size());
            ExpressionPointer rightOpened = openOverLocalBinders(
                rightCursor, localBinders, localBinders.size());
            // BOUNDED-fuel endpoint probes (kDefeqProbeFuel). Locating the
            // diff only needs to recognise when a cursor IS a user-proof
            // endpoint — a cheap structural / shallow-defeq hit. A probe at a
            // NON-matching position can otherwise reduce a heavy subterm (a
            // degree-4 complex power, say) wide enough to exhaust memory; the
            // cap makes the kernel answer a conservative `false` instead, and
            // the walk descends structurally to where the match is cheap.
            bool forwardMatch =
                isDefinitionallyEqual(environment_, openedContext,
                                       leftOpened, userLeftOpened,
                                       kDefeqProbeFuel)
                && isDefinitionallyEqual(environment_, openedContext,
                                          rightOpened, userRightOpened,
                                          kDefeqProbeFuel);
            if (forwardMatch) {
                innerProof = userProof;
                break;
            }
            bool symmetricMatch =
                isDefinitionallyEqual(environment_, openedContext,
                                       leftOpened, userRightOpened,
                                       kDefeqProbeFuel)
                && isDefinitionallyEqual(environment_, openedContext,
                                          rightOpened, userLeftOpened,
                                          kDefeqProbeFuel);
            if (symmetricMatch) {
                // The cursor endpoints are the user proof's endpoints
                // SWAPPED, so wrap with Equality.symmetry. userCarrier /
                // userLeft / userRight are already CLOSED over the local
                // binders — extractEqualityComponents read them off the
                // closed userProofType, and the `*Opened` values above are
                // separate opened copies used only for the defeq probe — so
                // they must NOT be closed again (doing so double-shifts the
                // local-hypothesis BoundVariables out of scope: the historic
                // symmetry-flip "bare BoundVariable" bug). With
                // userProof : userLeft = userRight,
                // symmetry(A, userLeft, userRight, userProof) : userRight =
                // userLeft — matching the swapped cursor endpoints.
                ExpressionPointer symmetryCall = makeConstant(
                    "Equality.symmetry", {userCarrierLevel});
                symmetryCall = makeApplication(
                    std::move(symmetryCall), userCarrier);
                symmetryCall = makeApplication(
                    std::move(symmetryCall), userLeft);
                symmetryCall = makeApplication(
                    std::move(symmetryCall), userRight);
                symmetryCall = makeApplication(
                    std::move(symmetryCall), userProof);
                innerProof = std::move(symmetryCall);
                break;
            }
            // Descend through Application nodes. If structural compare
            // bails (neither function nor argument structurally equal),
            // retry once after WHNF — unfolds Definition heads (e.g.
            // `Rational.subtract` → `+`/`negate`) and exposes reduced
            // App spines (`Natural.add(successor(_), _)` → `successor(
            // Natural.add(_, _))`). The reconstruction below uses the
            // post-WHNF saved sides; the resulting proof type is
            // definitionally equal to the original calc-step type, so
            // the caller's coercion accepts it.
            auto descendOrWhnf = [&]() -> bool {
                auto* leftApp =
                    std::get_if<Application>(&leftCursor->node);
                auto* rightApp =
                    std::get_if<Application>(&rightCursor->node);
                if (leftApp && rightApp) {
                    bool functionEqual = structurallyEqual(
                        leftApp->function, rightApp->function);
                    bool argumentEqual = structurallyEqual(
                        leftApp->argument, rightApp->argument);
                    if (functionEqual && argumentEqual) return false;
                    if (functionEqual) {
                        pathStepsOutsideIn.push_back(
                            {CalcCongruencePathStep::Kind::Arg,
                             leftApp->function});
                        leftCursor = leftApp->argument;
                        rightCursor = rightApp->argument;
                        return true;
                    }
                    if (argumentEqual) {
                        pathStepsOutsideIn.push_back(
                            {CalcCongruencePathStep::Kind::Fn,
                             leftApp->argument});
                        leftCursor = leftApp->function;
                        rightCursor = rightApp->function;
                        return true;
                    }
                }
                ExpressionPointer leftWhnf = weakHeadNormalForm(
                    environment_, leftCursor);
                ExpressionPointer rightWhnf = weakHeadNormalForm(
                    environment_, rightCursor);
                bool leftChanged =
                    !structurallyEqual(leftWhnf, leftCursor);
                bool rightChanged =
                    !structurallyEqual(rightWhnf, rightCursor);
                if (!leftChanged && !rightChanged) return false;
                leftCursor = leftWhnf;
                rightCursor = rightWhnf;
                return true;
            };
            if (!descendOrWhnf()) break;
        }
        if (!innerProof) {
            // The single-position descent found no slot. Fall back to
            // bounded combining: rewrite one endpoint by the cited fact
            // and let the auto-prover close the residual from context.
            return tryCombineCitedWithContext(
                localBinders, previousKernel, nextKernel, userProof,
                userLeft, userRight, userCarrier, userCarrierLevel,
                line, column);
        }
        // Wrap from innermost out with Equality.congruence (shared with
        // autoProveCalcStepRaw via wrapCongruenceChainOutsideIn).
        ExpressionPointer currentProof = wrapCongruenceChainOutsideIn(
            localBinders, pathStepsOutsideIn, leftCursor, rightCursor,
            innerProof);
        if (!currentProof) return nullptr;
        // Output contract (WS5/WS8): the symmetric-match + nested-congruence
        // wrapping above can, on some flips, build a term with an escaped
        // Internal FreeVariable (e.g. an opened-but-not-reclosed endpoint).
        // A calc-step proof is supposed to be CLOSED over the local binders
        // (those appear as de Bruijn indices), so any free variable is a
        // bug; left unchecked it surfaces downstream as a "kernel: unbound
        // internal variable" leak. (inferTypeInLocalContext does NOT catch
        // it — opening over the local binders re-supplies a same-named free
        // variable, so the ill-formed term type-checks here yet fails later
        // in a different context.) Reject it so the caller falls through to
        // its surface "type mismatch" path.
        if (containsFreeVariable(currentProof)) return nullptr;
        return currentProof;
    }

ExpressionPointer Elaborator::tryApplyBareLemmaToDiff(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer bareLemma,
        ExpressionPointer bareLemmaType,
        int line, int column) {
        // Open every leading Pi of the lemma as a fresh metavariable; what
        // remains is the conclusion (expected to be an equality whose
        // endpoints mention those metavariables).
        std::set<std::string> metavariableNames;
        std::vector<std::string> argumentNames;
        // The type of each argument binder, in terms of the earlier
        // `_diffLemmaArg_` metavariables — used to discharge propositional
        // side conditions (binders that don't appear in the conclusion, e.g.
        // an `i ≠ 0` hypothesis) from the local context after unification.
        std::vector<ExpressionPointer> argumentTypes;
        ExpressionPointer cursor = bareLemmaType;
        int index = 0;
        while (auto* pi = std::get_if<Pi>(&cursor->node)) {
            std::string fresh = "_diffLemmaArg_" + std::to_string(index++);
            metavariableNames.insert(fresh);
            argumentNames.push_back(fresh);
            argumentTypes.push_back(pi->domain);
            cursor = openBinder(pi->codomain, fresh,
                                 FreeVariableOrigin::Internal);
        }
        if (argumentNames.empty()) return nullptr;
        EqualityComponents conclusion;
        try {
            conclusion = extractEqualityComponents(
                weakHeadNormalForm(environment_, cursor),
                "argument-free citation diff", line);
        } catch (const ElaborateError&) {
            return nullptr;
        }
        // Walk `previous`/`next` down their shared application context. At
        // EACH differing level — outermost first — try to solve the lemma's
        // arguments by unifying its conclusion endpoints against that level's
        // `(fromTerm, toTerm)`. The first level that fully solves is where the
        // cited lemma's equation lives. Trying outermost-first matters: a
        // structural descent that always peels the single differing child
        // overshoots when a lemma matches a whole subterm whose head differs
        // but which happens to share a trailing argument with its counterpart
        // (e.g. `modulus·q` vs `x·(x·q) + q`, both ending in `q`).
        ExpressionPointer fromTerm =
            zetaUnfoldLetBinders(previousKernel, localBinders);
        ExpressionPointer toTerm =
            zetaUnfoldLetBinders(nextKernel, localBinders);
        while (true) {
            // Strongest attempt first: prove THIS diff level's subterm
            // equality by citing the lemma through the same goal-driven
            // instantiation a `by <lemma>` calc step uses
            // (`autoFillHintForClaim`). Unlike the local unify+discharge
            // below, it back-infers a lemma's NON-conclusion DATA arguments
            // from the context — e.g. an abstract ring bundle's
            // carrier/add/zero/one, recovered from an in-scope `IsRing`
            // hypothesis — which `unifyConstructorParameters` refuses to
            // bind (its value-free-var soundness guard). So an argument-free
            // citation works on a CONGRUENCE step over an abstract carrier;
            // the diff bridge then wraps the (sub)equality in the
            // surrounding congruence. At the OUTER level the lemma's
            // conclusion won't match a congruence wrapper, so this falls
            // through and we descend to the differing subterm.
            //
            // The sub-goal's carrier type must live in the SAME
            // closed-over-local scope as fromTerm/toTerm (BV references),
            // exactly as the calc machinery builds an `=` step goal: infer
            // it OPENED, then close. Skipping the close leaves carrier as a
            // free variable that won't structurally match the BV the bundle
            // hypothesis carries — so the lemma's data args never pin.
            try {
                ExpressionPointer carrierType = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, fromTerm),
                    localBinders, localBinders.size());
                LevelPointer carrierLevel =
                    typeUniverseOf(localBinders, fromTerm);
                ExpressionPointer levelGoal = makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Equality", {carrierLevel}),
                            carrierType),
                        fromTerm),
                    toTerm);
                ExpressionPointer filled = autoFillHintForClaim(
                    bareLemma, bareLemmaType, levelGoal, localBinders, line);
                if (filled) {
                    ExpressionPointer filledType =
                        inferTypeInLocalContext(localBinders, filled);
                    ExpressionPointer wrapped = tryDiffApplyUserProof(
                        localBinders, previousKernel, nextKernel,
                        filled, filledType, line, column);
                    if (wrapped) return wrapped;
                }
            } catch (const ElaborateError&) {
            } catch (const TypeError&) {
            }
            // Try the lemma at the current level, both orientations (it may
            // prove `subterm = other` or `other = subterm`).
            for (int orientation = 0; orientation < 2; ++orientation) {
                ExpressionPointer patternLeft = orientation == 0
                    ? conclusion.leftEndpoint : conclusion.rightEndpoint;
                ExpressionPointer patternRight = orientation == 0
                    ? conclusion.rightEndpoint : conclusion.leftEndpoint;
                std::map<std::string, ExpressionPointer> assignment;
                unifyConstructorParameters(patternLeft, fromTerm,
                                              metavariableNames, assignment);
                unifyConstructorParameters(patternRight, toTerm,
                                              metavariableNames, assignment);
                // Discharge any argument the conclusion didn't pin — a
                // propositional side condition (e.g. `i ≠ 0`) — by searching
                // the local hypotheses for a proof of its (now-instantiated)
                // type. Mirrors the lemma-index precondition discharge, so an
                // argument-free citation works on a congruence step whose
                // lemma carries hypotheses, not just bare equalities.
                {
                    Context openedContext =
                        buildContextFromLocalBinders(localBinders);
                    for (size_t a = 0; a < argumentNames.size(); ++a) {
                        if (assignment.count(argumentNames[a])) continue;
                        ExpressionPointer slotType = substituteFreeVariables(
                            argumentTypes[a], assignment, 0);
                        ExpressionPointer slotTypeOpened = openOverLocalBinders(
                            slotType, localBinders, localBinders.size());
                        ExpressionPointer slotTypeNormalised;
                        try {
                            slotTypeNormalised = weakHeadNormalForm(
                                environment_, slotTypeOpened);
                        } catch (const TypeError&) { continue; }
                        if (!typeIsProposition(openedContext,
                                                 slotTypeNormalised)) {
                            continue;
                        }
                        for (int j =
                                 static_cast<int>(localBinders.size()) - 1;
                             j >= 0; --j) {
                            ExpressionPointer candidateType =
                                openOverLocalBinders(
                                    localBinders[j].type, localBinders, j);
                            bool eq;
                            try {
                                eq = isDefinitionallyEqual(environment_,
                                    openedContext, candidateType,
                                    slotTypeNormalised);
                            } catch (const TypeError&) { eq = false; }
                            if (eq) {
                                assignment[argumentNames[a]] =
                                    makeBoundVariable(
                                        static_cast<int>(localBinders.size())
                                        - 1 - j);
                                break;
                            }
                        }
                    }
                }
                bool allSolved = true;
                for (const auto& name : argumentNames) {
                    if (!assignment.count(name)) { allSolved = false; break; }
                }
                if (!allSolved) continue;
                // Apply the lemma to the solved arguments and hand the now-
                // concrete proof to the ordinary diff bridge for the
                // congruence (and possible symmetry) wrapping.
                ExpressionPointer applied = bareLemma;
                for (const auto& name : argumentNames) {
                    applied = makeApplication(applied, assignment[name]);
                }
                ExpressionPointer appliedType;
                try {
                    appliedType =
                        inferTypeInLocalContext(localBinders, applied);
                } catch (const TypeError&) {
                    continue;
                } catch (const ElaborateError&) {
                    continue;
                }
                ExpressionPointer wrapped = tryDiffApplyUserProof(
                    localBinders, previousKernel, nextKernel,
                    applied, appliedType, line, column);
                if (wrapped) return wrapped;
            }
            // Not here: peel one matching component and retry deeper.
            auto* leftApp = std::get_if<Application>(&fromTerm->node);
            auto* rightApp = std::get_if<Application>(&toTerm->node);
            if (!leftApp || !rightApp) break;
            bool functionEqual = structurallyEqual(
                leftApp->function, rightApp->function);
            bool argumentEqual = structurallyEqual(
                leftApp->argument, rightApp->argument);
            if (functionEqual && !argumentEqual) {
                fromTerm = leftApp->argument;
                toTerm = rightApp->argument;
                continue;
            }
            if (argumentEqual && !functionEqual) {
                fromTerm = leftApp->function;
                toTerm = rightApp->function;
                continue;
            }
            break;
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryAcRearrangement(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        int line) {
        // Abstract `Ring.carrier(s)` rearrangements (the fingerprint plan's
        // Phase 1 win): `+` is AC and `·` associative in every ring, so a
        // pure sum-of-products rearrangement closes by direct AC
        // normalisation — no expensive context-equality-bridge search. The
        // registered-carrier `ring` below declines on this carrier, so try
        // the abstract normaliser first. It returns nullptr (no throw) when
        // the carrier isn't an abstract ring or the sides don't match.
        ExpressionPointer abstractProof = proveAbstractRingAC(
            localBinders, previousKernel, nextKernel,
            carrierType, carrierLevel, line);
        if (abstractProof) return abstractProof;
        ExpressionPointer expectedType = makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality", {carrierLevel}),
                    carrierType),
                previousKernel),
            nextKernel);
        try {
            return elaborateRing(localBinders, expectedType, line, 0);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
    }

bool Elaborator::matchAgainstPattern(
        ExpressionPointer pattern,
        ExpressionPointer subject,
        int binderCount,
        std::vector<ExpressionPointer>& bindings,
        int piDepth,
        std::vector<DeferredProjectionMatch>* deferredOut) {
        // Canonical-bundle resolution: pattern `<Structure>.carrier(BV(slot))`
        // against a concrete carrier `subject`. Bind `slot` to the canonical
        // bundle registered for `(Structure, head subject)` — letting an
        // implicit `{r : Ring}` be recovered from a concrete `Integer` /
        // `Polynomial(Integer, …)` operand during operator dispatch. Uses the
        // RAW subject head (a defined carrier like `Integer` WHNF-reduces to
        // its `Quotient(…)` body, which is not how it is registered). This
        // resolves only the unique registered bundle for a carrier — it never
        // coerces a value — and the kernel re-checks the assembled call.
        if (auto* patternApp = std::get_if<Application>(&pattern->node)) {
            if (auto* projection =
                    std::get_if<Constant>(&patternApp->function->node)) {
                auto* argumentBV = std::get_if<BoundVariable>(
                    &patternApp->argument->node);
                if (argumentBV
                    && argumentBV->deBruijnIndex >= piDepth
                    && argumentBV->deBruijnIndex < piDepth + binderCount) {
                    int slot = argumentBV->deBruijnIndex - piDepth;
                    const std::string suffix = ".carrier";
                    bool isCarrier = projection->name.size() > suffix.size()
                        && projection->name.compare(
                               projection->name.size() - suffix.size(),
                               suffix.size(), suffix) == 0;
                    // (1) `<S>.carrier(BV(slot))` with the slot still
                    //     unsolved: resolve it to the canonical bundle for
                    //     the concrete subject carrier. With a deferral
                    //     accumulator available (citation matching), DEFER
                    //     instead: the rest of the match may pin the slot
                    //     to a DIFFERENT bundle over the same carrier
                    //     (e.g. an unregistered `Real.ring`), which an
                    //     eager registry bind would poison; the registry
                    //     is consulted as the last resort during deferred
                    //     verification instead.
                    if (isCarrier && !bindings[slot]) {
                        if (deferredOut) {
                            if (piDepth > 0
                                && referencesAnyBoundInRange(
                                       subject, 0, piDepth)) {
                                return false;
                            }
                            deferredOut->push_back(
                                DeferredProjectionMatch{
                                    patternApp->function, slot,
                                    piDepth > 0
                                        ? liftBoundVariables(
                                              subject, -piDepth, 0)
                                        : subject});
                            return true;
                        }
                        std::string structure = projection->name.substr(
                            0, projection->name.size() - suffix.size());
                        auto entry =
                            environment_.canonicalBundleRegistry.find(
                                std::make_tuple(structure,
                                    headConstantName(subject)));
                        if (entry
                            != environment_.canonicalBundleRegistry.end()) {
                            bindings[slot] = makeConstant(entry->second);
                            return true;
                        }
                    }
                    // Any OTHER projection of a metavariable slot —
                    //     `Ring.zero(r)`, `Ring.one(r)`, … — is handled on
                    //     the FAILURE path by tryProjectionFallback:
                    //     definitional equality once the slot is bound
                    //     (`Ring.zero(Real.ring) ≡ Real.zero` is a plain
                    //     unfold-then-project chain), deferral when it is
                    //     not. Keeping it off the success path leaves the
                    //     structural fast path untouched. (This subsumes
                    //     the old registered-canonical-bundle special
                    //     case, which could not see e.g. `Real.ring` —
                    //     a Ring bundle that is not instance-registered.)
                }
            }
        }
        if (auto* patternBV =
                std::get_if<BoundVariable>(&pattern->node)) {
            int idx = patternBV->deBruijnIndex;
            if (idx >= piDepth && idx < piDepth + binderCount) {
                int slot = idx - piDepth;
                // The subject must live in the OUTER scope (no
                // references to the piDepth local Pi binders); else
                // the binding would be unground when the lemma is
                // applied. Detect and bail.
                if (piDepth > 0
                    && referencesAnyBoundInRange(
                           subject, 0, piDepth)) {
                    return false;
                }
                // Shift the subject down by piDepth so it lives in
                // the same scope as the other bindings (the
                // lemma-application context).
                ExpressionPointer shiftedSubject = piDepth > 0
                    ? liftBoundVariables(subject, -piDepth, 0)
                    : subject;
                if (!bindings[slot]) {
                    bindings[slot] = shiftedSubject;
                    return true;
                }
                if (structurallyEqual(bindings[slot], shiftedSubject)) {
                    return true;
                }
                // The same slot can be pinned once from a FOLDED occurrence
                // and once from an UNFOLDED one and still be consistent: a
                // recursive definition's tail comes back as `range_down(k)`
                // from one side of the goal, but as the raw recursor IH
                // `Natural_recursor(… k)` after the OTHER side is
                // WHNF-unfolded to expose a constructor head (`prepend`).
                // The two are definitionally equal; accept on a δ/ι-aware
                // check. Empty context: any free bound variables act as
                // opaque atoms and the bridging reduction is
                // context-independent (same pattern as the projection
                // resolution below). Additive — only reached when the
                // structural check already failed, so it can widen matches
                // but never narrow them.
                try {
                    return isDefinitionallyEqual(
                        environment_, Context{},
                        bindings[slot], shiftedSubject);
                } catch (const TypeError&) {
                    return false;
                }
            }
            // idx < piDepth: descended Pi binder; idx >=
            // piDepth + binderCount: outer-scope binder. Either
            // way, subject must be the same BV index.
            auto* s = std::get_if<BoundVariable>(&subject->node);
            return s && s->deBruijnIndex == idx;
        }
        if (pattern->node.index() != subject->node.index()) {
            // Kind mismatch — try WHNF on the subject. A δ-defined
            // head (e.g. `Integer.LessOrEqual` unfolding to an
            // `Exists`) might expose the shape the pattern wants.
            // Progress must be checked STRUCTURALLY, not by pointer:
            // with the kernel caches disabled, WHNF of an already-normal
            // term rebuilds an equal-but-fresh pointer every call, and a
            // pointer test recurses here forever (stack-overflow SIGSEGV).
            ExpressionPointer subjectWhnf = weakHeadNormalForm(
                environment_, subject);
            if (subjectWhnf.get() != subject.get()
                && !structurallyEqual(subjectWhnf, subject)) {
                return matchAgainstPattern(
                    pattern, subjectWhnf,
                    binderCount, bindings, piDepth, deferredOut);
            }
            return tryProjectionFallback(
                pattern, subject, binderCount, bindings, piDepth,
                deferredOut);
        }
        if (auto* p = std::get_if<BoundVariable>(&pattern->node)) {
            (void)p;
            // Handled above; this branch is for the
            // (pattern is non-BV but subject is BV) reject case.
            return false;
        }
        if (auto* p = std::get_if<FreeVariable>(&pattern->node)) {
            auto* s = std::get_if<FreeVariable>(&subject->node);
            return p->name == s->name && p->origin == s->origin;
        }
        if (auto* p = std::get_if<Sort>(&pattern->node)) {
            auto* s = std::get_if<Sort>(&subject->node);
            return levelsDefinitionallyEqual(p->level, s->level);
        }
        if (auto* p = std::get_if<Application>(&pattern->node)) {
            // Deferred entries appended by a failing attempt below must
            // roll back with the bindings they accompanied.
            size_t deferredMark = deferredOut ? deferredOut->size() : 0;
            auto* s = std::get_if<Application>(&subject->node);
            if (s) {
                // Structural attempt — bindings is scratch; save in
                // case we need to retry after WHNF.
                std::vector<ExpressionPointer> savedBindings =
                    bindings;
                if (matchAgainstPattern(
                        p->function, s->function,
                        binderCount, bindings, piDepth, deferredOut)
                    && matchAgainstPattern(
                        p->argument, s->argument,
                        binderCount, bindings, piDepth, deferredOut)) {
                    return true;
                }
                bindings = savedBindings;
                if (deferredOut) deferredOut->resize(deferredMark);
            }
            // Structural failed (or subject kinds disagreed). Unfold the
            // subject's defined head ONE step at a time and retry: full
            // WHNF can reduce PAST the head the pattern wants (e.g. a
            // pattern `filter(P, list)` against `coprime_residues(n)` —
            // one δβ exposes the filter, but WHNF would continue into
            // filter's recursor, stuck on the neutral list). Each step
            // re-runs the full match, so intermediate heads get their
            // chance.
            {
                ExpressionPointer unfolded = subject;
                for (int step = 0; step < 8; ++step) {
                    ExpressionPointer next =
                        unfoldHeadConstantOneStep(unfolded);
                    if (!next || next.get() == unfolded.get()
                        || structurallyEqual(next, unfolded)) break;
                    unfolded = next;
                    std::vector<ExpressionPointer> retryBindings =
                        bindings;
                    if (matchAgainstPattern(
                            pattern, unfolded,
                            binderCount, retryBindings, piDepth,
                            deferredOut)) {
                        bindings = std::move(retryBindings);
                        return true;
                    }
                    if (deferredOut) deferredOut->resize(deferredMark);
                }
            }
            // Last resort: full WHNF (δ/β/ι) — catches reductions the
            // pure-δ walk above cannot (e.g. `successor(p) * q` →
            // `q + p*q`). Bail if it makes no progress — checked
            // STRUCTURALLY, not by pointer (see the kind-mismatch site
            // above: a pointer test loops forever with caches disabled).
            ExpressionPointer subjectWhnf = weakHeadNormalForm(
                environment_, subject);
            if (subjectWhnf.get() != subject.get()
                && !structurallyEqual(subjectWhnf, subject)) {
                return matchAgainstPattern(
                    pattern, subjectWhnf,
                    binderCount, bindings, piDepth, deferredOut);
            }
            return tryProjectionFallback(
                pattern, subject, binderCount, bindings, piDepth,
                deferredOut);
        }
        if (auto* p = std::get_if<Constant>(&pattern->node)) {
            auto* s = std::get_if<Constant>(&subject->node);
            if (p->name != s->name) return false;
            if (p->universeArguments.size()
                    != s->universeArguments.size()) {
                return false;
            }
            for (size_t i = 0; i < p->universeArguments.size(); ++i) {
                if (!levelsDefinitionallyEqual(
                        p->universeArguments[i],
                        s->universeArguments[i])) {
                    return false;
                }
            }
            return true;
        }
        if (auto* p = std::get_if<Pi>(&pattern->node)) {
            auto* s = std::get_if<Pi>(&subject->node);
            // The Pi binder itself is a local fresh variable in both
            // pattern and subject; recurse into domain at the same
            // piDepth (the binder isn't visible from its own domain)
            // and into codomain at piDepth + 1.
            return matchAgainstPattern(p->domain, s->domain,
                                          binderCount, bindings, piDepth,
                                          deferredOut)
                && matchAgainstPattern(p->codomain, s->codomain,
                                          binderCount, bindings,
                                          piDepth + 1, deferredOut);
        }
        if (auto* p = std::get_if<Lambda>(&pattern->node)) {
            // Same binder bookkeeping as Pi. A lambda shows up on the
            // pattern side once a conclusion is δ-unfolded to a binder-
            // carrying head — e.g. `Natural.divides a b` unfolds to
            // `Exists Natural (λ q. b = a * q)`, whose predicate is a
            // lambda. Recurse into the body at piDepth + 1 so the data
            // binders inside still pin (this is what lets a cited lemma
            // whose conclusion is a `definition` match a goal that has
            // already been unfolded — as a propositionless
            // `done`/`goal`/`okay` sees it past an eliminator motive).
            auto* s = std::get_if<Lambda>(&subject->node);
            if (!s) return false;
            return matchAgainstPattern(p->domain, s->domain,
                                          binderCount, bindings, piDepth,
                                          deferredOut)
                && matchAgainstPattern(p->body, s->body,
                                          binderCount, bindings,
                                          piDepth + 1, deferredOut);
        }
        // Let is rare in lemma LHSs and needs extra binder bookkeeping;
        // bail conservatively.
        return false;
    }

bool Elaborator::tryProjectionFallback(
        ExpressionPointer pattern,
        ExpressionPointer subject,
        int binderCount,
        std::vector<ExpressionPointer>& bindings,
        int piDepth,
        std::vector<DeferredProjectionMatch>* deferredOut) {
        // Only a pattern node `Proj(BV slot)` — a Constant applied to a
        // single metavariable — participates; anything else fails as the
        // structural walk decided.
        auto* patternApp = std::get_if<Application>(&pattern->node);
        if (!patternApp) return false;
        auto* projection =
            std::get_if<Constant>(&patternApp->function->node);
        if (!projection) return false;
        // Restrict to STRUCTURE-BUNDLE projections (`Ring.zero`,
        // `Ring.carrier`, … — a name `S.field` where `S.carrier` is in
        // scope). This is the whole seam, and it keeps the fallback off
        // the prover's hot failure paths: a mismatching `successor(n)` /
        // `negate(x)` node must keep failing instantly, not spend a
        // definitional-equality check (or a deferred slot) to learn the
        // same thing. Measured cost of the ungated version: 2x on
        // Real/supremum.
        {
            size_t lastDot = projection->name.rfind('.');
            if (lastDot == std::string::npos) return false;
            std::string structure = projection->name.substr(0, lastDot);
            if (structure.empty()
                || environment_.lookup(structure + ".carrier") == nullptr) {
                return false;
            }
        }
        auto* argumentBV =
            std::get_if<BoundVariable>(&patternApp->argument->node);
        if (!argumentBV) return false;
        int idx = argumentBV->deBruijnIndex;
        if (idx < piDepth || idx >= piDepth + binderCount) return false;
        int slot = idx - piDepth;
        // Same scope discipline as a plain metavariable binding: the
        // subject must survive in the lemma-application context.
        if (piDepth > 0
            && referencesAnyBoundInRange(subject, 0, piDepth)) {
            return false;
        }
        ExpressionPointer shiftedSubject = piDepth > 0
            ? liftBoundVariables(subject, -piDepth, 0)
            : subject;
        if (bindings[slot]) {
            // Slot already pinned: the projection either reduces to the
            // subject or the node genuinely does not match.
            ExpressionPointer substituted = makeApplication(
                patternApp->function, bindings[slot]);
            try {
                return isDefinitionallyEqual(
                    environment_, Context{}, substituted, shiftedSubject);
            } catch (const TypeError&) {
                return false;
            }
        }
        if (!deferredOut) return false;
        deferredOut->push_back(
            DeferredProjectionMatch{
                patternApp->function, slot, shiftedSubject});
        return true;
    }

bool Elaborator::matchAgainstPatternWithDeferredProjections(
        ExpressionPointer pattern,
        ExpressionPointer subject,
        int binderCount,
        std::vector<ExpressionPointer>& bindings) {
        std::vector<DeferredProjectionMatch> deferred;
        if (!matchAgainstPattern(pattern, subject, binderCount, bindings,
                                  0, &deferred)) {
            return false;
        }
        // Resolution pass: a `<S>.carrier(BV slot)` node whose slot the
        // rest of the match did NOT pin falls back to the canonical-bundle
        // registry (the eager bind the bare matcher would have made).
        for (const auto& deferredMatch : deferred) {
            if (bindings[deferredMatch.slot]) continue;
            auto* projection = std::get_if<Constant>(
                &deferredMatch.projectionHead->node);
            if (!projection) continue;
            const std::string suffix = ".carrier";
            if (projection->name.size() <= suffix.size()
                || projection->name.compare(
                       projection->name.size() - suffix.size(),
                       suffix.size(), suffix) != 0) {
                continue;
            }
            std::string structure = projection->name.substr(
                0, projection->name.size() - suffix.size());
            auto entry = environment_.canonicalBundleRegistry.find(
                std::make_tuple(structure,
                    headConstantName(deferredMatch.subject)));
            if (entry != environment_.canonicalBundleRegistry.end()) {
                bindings[deferredMatch.slot] =
                    makeConstant(entry->second);
            }
        }
        // Second-chance resolution: a slot pinned ONLY by non-carrier
        // projections (`Ring.zero(r)`, `Ring.multiply(r, …)` — the
        // structure argument occurring nowhere outside projections, e.g.
        // citing Ring.zero_multiply_left at a concrete carrier) gets no
        // binding above. Try each registered bundle of the structure and
        // accept a UNIQUE candidate under which every deferred
        // projection for the slot verifies definitionally; reject on
        // ambiguity (two distinct bundles both verifying).
        for (const auto& deferredMatch : deferred) {
            if (bindings[deferredMatch.slot]) continue;
            auto* projection = std::get_if<Constant>(
                &deferredMatch.projectionHead->node);
            if (!projection) continue;
            std::size_t lastDot = projection->name.rfind('.');
            if (lastDot == std::string::npos) continue;
            std::string structure = projection->name.substr(0, lastDot);
            std::string uniqueBundle;
            bool ambiguous = false;
            std::set<std::string> tried;
            for (const auto& [registryKey, bundleName] :
                 environment_.canonicalBundleRegistry) {
                if (std::get<0>(registryKey) != structure) continue;
                if (!tried.insert(bundleName).second) continue;
                ExpressionPointer trial = makeConstant(bundleName);
                bool verifies = true;
                for (const auto& other : deferred) {
                    if (other.slot != deferredMatch.slot) continue;
                    ExpressionPointer substituted = makeApplication(
                        other.projectionHead, trial);
                    try {
                        if (!isDefinitionallyEqual(environment_, Context{},
                                substituted, other.subject)) {
                            verifies = false;
                            break;
                        }
                    } catch (const TypeError&) {
                        verifies = false;
                        break;
                    }
                }
                if (verifies) {
                    if (!uniqueBundle.empty()
                        && uniqueBundle != bundleName) {
                        ambiguous = true;
                        break;
                    }
                    uniqueBundle = bundleName;
                }
            }
            if (!ambiguous && !uniqueBundle.empty()) {
                bindings[deferredMatch.slot] = makeConstant(uniqueBundle);
            }
        }
        // Verification pass: every deferred projection must now reduce to
        // the subject it was provisionally matched against.
        for (const auto& deferredMatch : deferred) {
            if (!bindings[deferredMatch.slot]) return false;
            ExpressionPointer substituted = makeApplication(
                deferredMatch.projectionHead,
                bindings[deferredMatch.slot]);
            try {
                if (!isDefinitionallyEqual(environment_, Context{},
                        substituted, deferredMatch.subject)) {
                    return false;
                }
            } catch (const TypeError&) {
                return false;
            }
        }
        return true;
    }


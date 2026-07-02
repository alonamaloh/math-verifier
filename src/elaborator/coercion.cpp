// Out-of-line Elaborator method definitions: coercion-to-expected-type via diff + quotient/equivalence bridges
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::acceptCoercionIfClosed(
        ExpressionPointer wrapped,
        const std::vector<LocalBinder>& localBinders,
        const char* strategy) const {
        if (!wrapped) return nullptr;
        if (wrapped->maxFreeBoundVariable
                >= static_cast<int>(localBinders.size())) {
            std::cerr << "warning: internal: coerceToExpectedTypeViaDiff "
                         "strategy '" << strategy << "' produced a term that "
                         "is not closed over its local binders (a bound "
                         "variable escaped) — falling back to the unwrapped "
                         "term\n";
            return nullptr;
        }
        return wrapped;
    }

ExpressionPointer Elaborator::coerceToExpectedTypeViaRegistry(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer expectedTypeClosed) {
        if (environment_.coercionRegistry.empty()) return term;
        try {
            ExpressionPointer termTypeOpened =
                inferTypeInLocalContext(localBinders, term);
            ExpressionPointer expectedTypeOpened = openOverLocalBinders(
                expectedTypeClosed, localBinders, localBinders.size());
            Context context = buildContextFromLocalBinders(localBinders);
            if (isDefinitionallyEqual(environment_, context,
                                       termTypeOpened, expectedTypeOpened)) {
                return term;
            }
            // The registry is keyed on the source-level type head name
            // (`Natural`, `Integer`, …), not the unfolded representation, so
            // match on the raw head. `headConstantName` peels Applications so
            // parameterised types report their head.
            std::string termHead = headConstantName(termTypeOpened);
            std::string expectedHead = headConstantName(expectedTypeOpened);
            if (termHead.empty() || expectedHead.empty()) return term;
            auto entry = environment_.coercionRegistry.find(
                std::make_tuple(termHead, expectedHead));
            if (entry == environment_.coercionRegistry.end()) return term;
            return applyCoercionChain(std::move(term), entry->second);
        } catch (const TypeError&) {
            // term's type couldn't be inferred — leave it for the
            // authoritative use-site check to report.
            return term;
        }
    }

ExpressionPointer Elaborator::coerceToExpectedTypeViaDiff(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer expectedTypeClosed) {
        TimedScope _scope(*this, "coerceToExpectedTypeViaDiff");
        // Cheap structural prefilter. The full coerce path runs an
        // inferType + isDefinitionallyEqual upfront — ~1 ms per call on math-heavy
        // files — before attempting four sub-strategies:
        //   (a) tryDiffWrapForEqualityGoal    — expected WHNF head must be Equality
        //   (b) tryDiffBridgeViaContextEquality — needs a local Equality hypothesis
        //   (c) tryDoubleNegationElimination — term type must be Not(Not P)
        //   (d) tryBarePropositionAsProof    — term is structurally equal to expected
        //                                       (and has type Sort 0, but the
        //                                       structural-equality check filters out
        //                                       essentially all other shapes already)
        // For (a)/(b)/(d), all preconditions are cheap to test structurally
        // (head check on expected type, scan of binder type heads, pointer/
        // hash-compare on term vs expected). Strategy (c) is the lone holdout
        // — it requires inferType to confirm `Not(Not P)`, but the pattern
        // (suppose ¬P; … claim False; eliminate to P) is rare enough that we
        // skip it here. If a user hits that path they'll see a genuine type
        // error and can write `Logic.double_negation_eliminate(P, h)` directly.
        auto headIsEqualityConstant =
            [](ExpressionPointer e) {
                ExpressionPointer head = e;
                while (auto* app = std::get_if<Application>(&head->node)) {
                    head = app->function;
                }
                auto* constant = std::get_if<Constant>(&head->node);
                return constant && constant->name == "Equality";
            };
        bool expectedCouldFire = headIsEqualityConstant(expectedTypeClosed);
        if (!expectedCouldFire) {
            // The expected type may be a `definition` that unfolds to an
            // Equality — a custom relation `R a b := a = b`, or a quotient's
            // equivalence (`RationalEquivalent`, `IntegerEquivalent`). WHNF
            // once to expose the head so the diff-wrap strategy (which WHNFs
            // internally, line 34) still fires; without this the prefilter
            // bails and `done by h` cannot bridge `R b a` from `h : R a b`.
            expectedCouldFire = headIsEqualityConstant(
                weakHeadNormalForm(
                    environment_,
                    openOverLocalBinders(expectedTypeClosed, localBinders,
                                         localBinders.size())));
        }
        bool contextCouldFire = false;
        if (!expectedCouldFire) {
            for (const auto& binder : localBinders) {
                if (headIsEqualityConstant(binder.type)) {
                    contextCouldFire = true;
                    break;
                }
            }
        }
        // Strategy (d) cheap precondition: term structurally equals
        // expected type. We have to compare in a matching representation
        // — most callers pass `term` in closed-over-binders form (BV
        // indices) but `expectedTypeClosed` in already-opened form (FVs),
        // depending on where the expected type came from. openOver on
        // an already-opened type is a no-op, so the comparison is
        // representation-agnostic. structurallyEqual short-circuits on
        // hash mismatch, so this is O(1) on the common case where term
        // and expected obviously differ.
        bool barePropositionCouldFire = false;
        if (!expectedCouldFire && !contextCouldFire) {
            ExpressionPointer termOpened = openOverLocalBinders(
                term, localBinders, localBinders.size());
            ExpressionPointer expectedOpenedForCompare = openOverLocalBinders(
                expectedTypeClosed, localBinders, localBinders.size());
            barePropositionCouldFire =
                structurallyEqual(termOpened, expectedOpenedForCompare);
        }
        // Disjunction-injection prefilter: a proof of one disjunct where
        // `Or(A, B)` is expected wraps with the matching Or.introduce*.
        bool expectedIsOr = headConstantName(expectedTypeClosed) == "Or";
        if (!expectedCouldFire
            && !contextCouldFire
            && !barePropositionCouldFire
            && !expectedIsOr) {
            return term;
        }
        ExpressionPointer termTypeOpened;
        try {
            termTypeOpened = inferTypeInLocalContext(
                localBinders, term);
        } catch (const TypeError&) {
            return term;
        } catch (const ElaborateError&) {
            return term;
        }
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        if (isDefinitionallyEqual(environment_, openedContext,
                       termTypeOpened, expectedOpened)) {
            return term;
        }
        // Disjunction injection: `term` proves one disjunct of an expected
        // `Or(A, B)`. A targeted, cheap coercion — two defeq checks against
        // the disjuncts, then wrap the matching Or.introduce* — so a bare
        // proof of one side (`calc d ≤ … = n`) reads as mathematics. It runs
        // before the general diff strategies below, which would otherwise
        // flail on (and run away over) a disjunction goal.
        if (expectedIsOr) {
            auto disjuncts =
                [](const ExpressionPointer& orType) {
                    std::vector<ExpressionPointer> args;
                    ExpressionPointer head = orType;
                    while (auto* app = std::get_if<Application>(&head->node)) {
                        args.push_back(app->argument);
                        head = app->function;
                    }
                    std::reverse(args.begin(), args.end());
                    return args;
                };
            std::vector<ExpressionPointer> closedDisjuncts =
                disjuncts(expectedTypeClosed);
            std::vector<ExpressionPointer> openedDisjuncts =
                disjuncts(expectedOpened);
            if (closedDisjuncts.size() == 2 && openedDisjuncts.size() == 2) {
                const char* constructorName = nullptr;
                if (isDefinitionallyEqual(environment_, openedContext,
                        termTypeOpened, openedDisjuncts[0])) {
                    constructorName = "Or.introduceLeft";
                } else if (isDefinitionallyEqual(environment_, openedContext,
                        termTypeOpened, openedDisjuncts[1])) {
                    constructorName = "Or.introduceRight";
                }
                if (constructorName) {
                    ExpressionPointer injected = makeApplication(
                        makeApplication(
                            makeApplication(makeConstant(constructorName),
                                            closedDisjuncts[0]),
                            closedDisjuncts[1]),
                        term);
                    if (auto ok = acceptCoercionIfClosed(
                            injected, localBinders, "or-injection")) {
                        return ok;
                    }
                }
            }
        }
        ExpressionPointer termTypeClosed = closeOverLocalBinders(
            termTypeOpened, localBinders, localBinders.size());
        // Equality-of-classes (WS3): a proof of `R(x, y)` where
        // `mk(x) = mk(y)` is expected wraps with Quotient.equivalent_implies_equal.
        ExpressionPointer wrapped = tryQuotientSoundForClassEquality(
            localBinders, term, termTypeClosed, expectedTypeClosed);
        if (auto ok = acceptCoercionIfClosed(wrapped, localBinders,
                "quotient-sound")) return ok;
        // Try the diff-wrap (equality coercion via Equality.congruence).
        wrapped = tryDiffWrapForEqualityGoal(
            localBinders, term, termTypeClosed, expectedTypeClosed);
        if (auto ok = acceptCoercionIfClosed(wrapped, localBinders,
                "diff-wrap")) return ok;
        // Diff-bridge via a local equality hypothesis: when inferred
        // and expected types differ at a single position (a, b) and
        // `a = b` or `b = a` is in scope, wrap with
        // Equality.transport_proposition. Lets the user write the
        // bare term and skip explicit `rewrite(...)`.
        wrapped = tryDiffBridgeViaContextEquality(
            localBinders, term, termTypeClosed, expectedTypeClosed);
        if (auto ok = acceptCoercionIfClosed(wrapped, localBinders,
                "diff-bridge-via-context-equality")) return ok;
        // Classical LEM bridge: if term : ¬¬P and expected : P, wrap
        // with Logic.double_negation_eliminate. Lets `suppose ¬P as h;
        // …; claim False` at theorem body close a goal stated as P,
        // mirroring textbook reductio ad absurdum.
        wrapped = tryDoubleNegationElimination(
            localBinders, term, termTypeClosed, expectedTypeClosed);
        if (auto ok = acceptCoercionIfClosed(wrapped, localBinders,
                "double-negation-elimination")) return ok;
        // Bare-proposition-as-proof. When the user writes a Proposition
        // value (e.g. `N ≤ m`) where a proof of that proposition was
        // expected, and the written value is kernel-equal to the
        // expected type, dispatch the auto-prover. Reads as math:
        // `pointwiseBound(m, N ≤ m)` instead of `pointwiseBound(m,
        // given(N ≤ m))` or a contrived named binder. Mitigation
        // against silently fixing typos: we require kernel-equality
        // first, so an unrelated proposition still fails loudly.
        wrapped = tryBarePropositionAsProof(
            localBinders, term, termTypeOpened, expectedTypeClosed);
        if (auto ok = acceptCoercionIfClosed(wrapped, localBinders,
                "bare-proposition-as-proof")) return ok;
        return term;
    }

ExpressionPointer Elaborator::tryBarePropositionAsProof(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer termTypeOpened,
        ExpressionPointer expectedTypeClosed) {
        // termTypeOpened must be the Proposition sort (Sort 0).
        ExpressionPointer termTypeWhnf = weakHeadNormalForm(
            environment_, termTypeOpened);
        auto* termTypeSort = std::get_if<Sort>(&termTypeWhnf->node);
        if (!termTypeSort) return nullptr;
        auto* termTypeLevel = std::get_if<LevelConst>(
            &termTypeSort->level->node);
        if (!termTypeLevel || termTypeLevel->value != 0) return nullptr;
        // The written proposition (`term`) must be kernel-equal to
        // the expected type. Compare in the opened representation so
        // BoundVariables on both sides align against the same FreeVar
        // identities — comparing a closed term against an opened one
        // would always fail.
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        ExpressionPointer termOpened = openOverLocalBinders(
            term, localBinders, localBinders.size());
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        if (isDefinitionallyEqual(environment_, openedContext,
                                  termOpened, expectedOpened)) {
            // The written proposition IS the whole goal: auto-prove it.
            try {
                return autoProveClaim(
                    expectedTypeClosed, localBinders, /*line=*/0);
            } catch (const ElaborateError&) {
                return nullptr;
            } catch (const TypeError&) {
                return nullptr;
            }
        }
        // Otherwise the written proposition may state ONE DISJUNCT of an `Or`
        // goal — a readable way to discharge a case ("here, k = 0"). Auto-
        // prove that disjunct and inject the matching `Or.introduce*`. (A
        // non-trivial disjunct can instead be derived with a `calc`, which the
        // disjunction-injection coercion handles separately.)
        ExpressionPointer expectedWhnf = weakHeadNormalForm(
            environment_, expectedOpened);
        std::vector<ExpressionPointer> openedDisjuncts;
        {
            ExpressionPointer head = expectedWhnf;
            while (auto* app = std::get_if<Application>(&head->node)) {
                openedDisjuncts.push_back(app->argument);
                head = app->function;
            }
            std::reverse(openedDisjuncts.begin(), openedDisjuncts.end());
            auto* headConstant = std::get_if<Constant>(&head->node);
            if (!headConstant || headConstant->name != "Or"
                || openedDisjuncts.size() != 2) {
                return nullptr;
            }
        }
        const char* constructorName = nullptr;
        int matchedIndex = -1;
        if (isDefinitionallyEqual(environment_, openedContext,
                                  termOpened, openedDisjuncts[0])) {
            constructorName = "Or.introduceLeft";
            matchedIndex = 0;
        } else if (isDefinitionallyEqual(environment_, openedContext,
                                         termOpened, openedDisjuncts[1])) {
            constructorName = "Or.introduceRight";
            matchedIndex = 1;
        }
        if (!constructorName) return nullptr;
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer leftClosed =
            closeOverLocalBinders(openedDisjuncts[0], localBinders, N);
        ExpressionPointer rightClosed =
            closeOverLocalBinders(openedDisjuncts[1], localBinders, N);
        ExpressionPointer disjunctClosed =
            (matchedIndex == 0) ? leftClosed : rightClosed;
        ExpressionPointer disjunctProof;
        try {
            disjunctProof = autoProveClaim(
                disjunctClosed, localBinders, /*line=*/0);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
        return makeApplication(
            makeApplication(
                makeApplication(makeConstant(constructorName), leftClosed),
                rightClosed),
            disjunctProof);
    }

ExpressionPointer Elaborator::tryDoubleNegationElimination(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer termTypeClosed,
        ExpressionPointer expectedTypeClosed) {
        if (!environment_.lookup(
                "Logic.double_negation_eliminate")) {
            return nullptr;
        }
        ExpressionPointer termTypeOpened = openOverLocalBinders(
            termTypeClosed, localBinders, localBinders.size());
        ExpressionPointer outerWhnf = weakHeadNormalForm(
            environment_, termTypeOpened);
        auto* outerPi = std::get_if<Pi>(&outerWhnf->node);
        if (!outerPi) return nullptr;
        // The outer Pi's codomain lives under its binder; if it
        // mentions BoundVariable(0) it isn't a Not-shape. We check
        // by WHNF'ing and verifying it's the constant `False` (which
        // doesn't reference the binder).
        ExpressionPointer outerCodomainWhnf = weakHeadNormalForm(
            environment_, outerPi->codomain);
        auto* outerCodomainConst = std::get_if<Constant>(
            &outerCodomainWhnf->node);
        if (!outerCodomainConst
            || outerCodomainConst->name != "False") {
            return nullptr;
        }
        // The inner Pi: domain of the outer is `Not(P) = P → False`.
        ExpressionPointer innerWhnf = weakHeadNormalForm(
            environment_, outerPi->domain);
        auto* innerPi = std::get_if<Pi>(&innerWhnf->node);
        if (!innerPi) return nullptr;
        ExpressionPointer innerCodomainWhnf = weakHeadNormalForm(
            environment_, innerPi->codomain);
        auto* innerCodomainConst = std::get_if<Constant>(
            &innerCodomainWhnf->node);
        if (!innerCodomainConst
            || innerCodomainConst->name != "False") {
            return nullptr;
        }
        // Inner Pi's domain is the P we need to match. Compare
        // against the opened expected type.
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        if (!isDefinitionallyEqual(environment_, openedContext,
                                     innerPi->domain, expectedOpened)) {
            return nullptr;
        }
        // Build the call: Logic.double_negation_eliminate(P, term).
        ExpressionPointer call = makeConstant(
            "Logic.double_negation_eliminate", {});
        call = makeApplication(call, expectedTypeClosed);
        call = makeApplication(call, term);
        return call;
    }

std::pair<ExpressionPointer, ExpressionPointer>
    Elaborator::findUniqueDiffPair(
        ExpressionPointer left, ExpressionPointer right) {
        ExpressionPointer pairA;
        ExpressionPointer pairB;
        bool failed = false;
        std::function<void(ExpressionPointer, ExpressionPointer)> walk =
            [&](ExpressionPointer l, ExpressionPointer r) {
                if (failed) return;
                if (structurallyEqual(l, r)) return;
                auto* leftApp =
                    std::get_if<Application>(&l->node);
                auto* rightApp =
                    std::get_if<Application>(&r->node);
                if (!leftApp || !rightApp) {
                    if (!pairA) {
                        pairA = l;
                        pairB = r;
                    } else if (!structurallyEqual(l, pairA)
                               || !structurallyEqual(r, pairB)) {
                        failed = true;
                    }
                    return;
                }
                walk(leftApp->function, rightApp->function);
                walk(leftApp->argument, rightApp->argument);
            };
        walk(left, right);
        if (failed || !pairA) return {nullptr, nullptr};
        return {pairA, pairB};
    }

ExpressionPointer Elaborator::tryDiffBridgeViaContextEquality(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer termTypeClosed,
        ExpressionPointer expectedTypeClosed) {
        if (!environment_.lookup("Equality.transport_proposition")) {
            return nullptr;
        }
        // Normalize both type inputs to canonical closed form via an
        // open-then-close round-trip. Some callers pass types that
        // are already partly-opened (e.g. `pi->domain` from an
        // inferred head type carries FVs for the local binders); the
        // open step is a no-op on those FVs, and the close step
        // converts every matching FV back to its BV. For truly-closed
        // inputs, open creates FVs and close puts them right back,
        // also a no-op. Either way the result is canonically closed.
        termTypeClosed = closeOverLocalBinders(
            openOverLocalBinders(termTypeClosed, localBinders,
                                 localBinders.size()),
            localBinders, localBinders.size());
        expectedTypeClosed = closeOverLocalBinders(
            openOverLocalBinders(expectedTypeClosed, localBinders,
                                 localBinders.size()),
            localBinders, localBinders.size());
        // Open both types so we can run the diff walker (FreeVariables
        // in place of de Bruijn indices for the surrounding binders).
        ExpressionPointer termTypeOpened = openOverLocalBinders(
            termTypeClosed, localBinders, localBinders.size());
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        auto whnf = [&](ExpressionPointer e) {
            return weakHeadNormalForm(environment_, e);
        };
        ExpressionPointer termTypeWhnf = whnf(termTypeOpened);
        ExpressionPointer expectedWhnf = whnf(expectedOpened);
        struct Pair { ExpressionPointer t; ExpressionPointer e; };
        Pair tries[4] = {
            {termTypeOpened, expectedOpened},
            {termTypeWhnf,   expectedOpened},
            {termTypeOpened, expectedWhnf},
            {termTypeWhnf,   expectedWhnf},
        };
        ExpressionPointer diffInferredOpened, diffExpectedOpened;
        ExpressionPointer expectedFormUsed = expectedOpened;
        for (const Pair& p : tries) {
            auto pr = findUniqueDiffPair(p.t, p.e);
            if (pr.first && pr.second) {
                diffInferredOpened = pr.first;
                diffExpectedOpened = pr.second;
                expectedFormUsed = p.e;
                break;
            }
        }
        if (!diffInferredOpened || !diffExpectedOpened) return nullptr;

        // Find an equation in local context whose endpoints match the
        // diff pair (forward or symmetric). On match, return a closed-
        // form Equality components record + the bound-variable proof
        // (or its symmetry wrap), all ready to splice into the
        // transport_proposition call.
        struct EqCandidate {
            ExpressionPointer carrierTypeOpened;
            LevelPointer carrierLevel;
            // Built in closed scope (BoundVariable to local binder).
            ExpressionPointer proofClosed;
        };
        auto findEquationInContext = [&]() -> std::optional<EqCandidate> {
            int N = static_cast<int>(localBinders.size());
            for (int b = N - 1; b >= 0; --b) {
                ExpressionPointer binderTypeOpened = openOverLocalBinders(
                    localBinders[b].type, localBinders, (size_t)b);
                ExpressionPointer binderTypeWhnf =
                    weakHeadNormalForm(environment_, binderTypeOpened);
                EqualityComponents components;
                try {
                    components = extractEqualityComponents(
                        binderTypeWhnf,
                        "diff-bridge equality candidate", 0);
                } catch (const ElaborateError&) {
                    continue;
                }
                bool forwardMatch =
                    structurallyEqual(
                        components.leftEndpoint, diffInferredOpened)
                    && structurallyEqual(
                        components.rightEndpoint, diffExpectedOpened);
                bool symmetricMatch =
                    structurallyEqual(
                        components.leftEndpoint, diffExpectedOpened)
                    && structurallyEqual(
                        components.rightEndpoint, diffInferredOpened);
                if (!forwardMatch && !symmetricMatch) continue;
                ExpressionPointer hypProofClosed =
                    makeBoundVariable(N - 1 - b);
                // Close the diff endpoints for use in the symmetry
                // wrap (when needed) and for the eventual transport.
                ExpressionPointer diffInferredClosed =
                    closeOverLocalBinders(diffInferredOpened,
                        localBinders, localBinders.size());
                ExpressionPointer diffExpectedClosed =
                    closeOverLocalBinders(diffExpectedOpened,
                        localBinders, localBinders.size());
                ExpressionPointer carrierTypeClosed =
                    closeOverLocalBinders(components.carrierType,
                        localBinders, localBinders.size());
                ExpressionPointer proofClosed;
                if (forwardMatch) {
                    proofClosed = std::move(hypProofClosed);
                } else {
                    ExpressionPointer sym = makeConstant(
                        "Equality.symmetry",
                        {components.carrierUniverseLevel});
                    sym = makeApplication(
                        std::move(sym), carrierTypeClosed);
                    sym = makeApplication(
                        std::move(sym), std::move(diffExpectedClosed));
                    sym = makeApplication(
                        std::move(sym),
                        // Re-close (already closed but cheap).
                        closeOverLocalBinders(diffInferredOpened,
                            localBinders, localBinders.size()));
                    sym = makeApplication(
                        std::move(sym), std::move(hypProofClosed));
                    proofClosed = std::move(sym);
                }
                EqCandidate result;
                result.carrierTypeOpened = components.carrierType;
                result.carrierLevel = components.carrierUniverseLevel;
                result.proofClosed = std::move(proofClosed);
                return result;
            }
            return std::nullopt;
        };

        auto candidate = findEquationInContext();
        if (!candidate) return nullptr;

        // Close the diff pair and carrier for splicing into the final
        // call. From here on we work in CLOSED form so the motive
        // lambda we build has BV(0) referring to its own binder (and
        // other BVs referring to the surrounding local binders,
        // shifted by 1 to make room).
        ExpressionPointer diffInferredClosed = closeOverLocalBinders(
            diffInferredOpened, localBinders, localBinders.size());
        ExpressionPointer diffExpectedClosed = closeOverLocalBinders(
            diffExpectedOpened, localBinders, localBinders.size());
        ExpressionPointer carrierTypeClosed = closeOverLocalBinders(
            candidate->carrierTypeOpened, localBinders,
            localBinders.size());

        // Choose the closed form of expectedType corresponding to
        // whichever form the diff walker used. The diff walker may
        // have used the WHNF expansion; we mirror that by WHNF-ing
        // the closed form (kernel WHNF over an empty context is the
        // same shape as WHNF over the local context modulo FVs).
        Context openedContext = buildContextFromLocalBinders(localBinders);
        ExpressionPointer expectedFormUsedClosed = expectedTypeClosed;
        if (expectedFormUsed.get() == expectedWhnf.get()) {
            expectedFormUsedClosed = weakHeadNormalForm(
                environment_, expectedTypeClosed);
        }
        // termType closed form, in the same combo as the diff walker
        // used (unreduced vs WHNF).
        ExpressionPointer termTypeFormClosed = termTypeClosed;
        // (We don't bother re-WHNFing termType here; the isDefEq check
        // below sees through definitional unfoldings either way.)

        // Compute total occurrences using `abstractStructuralOccurrence`
        // on the closed form (target = diffExpectedClosed). The body
        // it produces has BV(0) at every matched position with other
        // BVs shifted up by 1 — exactly the form needed inside a
        // lambda wrapper.
        int totalOccurrences = 0;
        ExpressionPointer probeBody = abstractStructuralOccurrence(
            expectedFormUsedClosed, diffExpectedClosed,
            /*currentDepth=*/0, totalOccurrences);
        (void)probeBody;
        if (totalOccurrences == 0) return nullptr;

        std::vector<uint32_t> masksToTry;
        if (totalOccurrences <= 16) {
            uint32_t allMask = (1u << totalOccurrences) - 1;
            masksToTry.push_back(allMask);
            for (int i = 0; i < totalOccurrences; ++i) {
                if ((1u << i) != allMask) {
                    masksToTry.push_back(1u << i);
                }
            }
            for (uint32_t s = 1; s < allMask; ++s) {
                if (__builtin_popcount(s) >= 2) {
                    masksToTry.push_back(s);
                }
            }
        } else {
            masksToTry.push_back((uint32_t)((1ull << 16) - 1));
        }

        for (uint32_t mask : masksToTry) {
            int counter = 0;
            ExpressionPointer motiveBodyClosed =
                abstractStructuralOccurrenceMasked(
                    expectedFormUsedClosed, diffExpectedClosed,
                    /*currentDepth=*/0, counter, mask);
            // motive(diffInferred): substitute diffInferredClosed
            // for BV(0). Then compare with termType in opened form.
            ExpressionPointer motiveAppliedClosed = substitute(
                motiveBodyClosed, 0, diffInferredClosed);
            ExpressionPointer motiveAppliedOpened = openOverLocalBinders(
                motiveAppliedClosed, localBinders, localBinders.size());
            if (!isDefinitionallyEqual(environment_, openedContext,
                    motiveAppliedOpened, termTypeOpened)) {
                continue;
            }
            ExpressionPointer motiveLambda = makeLambda(
                "_diffBridge", carrierTypeClosed,
                std::move(motiveBodyClosed));
            ExpressionPointer call = makeConstant(
                "Equality.transport_proposition",
                {candidate->carrierLevel});
            call = makeApplication(std::move(call), carrierTypeClosed);
            call = makeApplication(std::move(call), std::move(motiveLambda));
            call = makeApplication(std::move(call), diffInferredClosed);
            call = makeApplication(std::move(call), diffExpectedClosed);
            call = makeApplication(std::move(call), candidate->proofClosed);
            call = makeApplication(std::move(call), term);
            // Sanity-check: the constructed term must type-check and
            // its inferred type must match the expected type. If not,
            // this candidate motive was wrong; try the next subset.
            try {
                ExpressionPointer callType =
                    inferTypeInLocalContext(localBinders, call);
                ExpressionPointer callTypeOpened = openOverLocalBinders(
                    callType, localBinders, localBinders.size());
                if (isDefinitionallyEqual(environment_, openedContext,
                        callTypeOpened, expectedOpened)) {
                    return call;
                }
            } catch (const TypeError&) {
                // fall through to next mask
            } catch (const ElaborateError&) {
                // fall through to next mask
            }
        }
        return nullptr;
    }

bool Elaborator::peelQuotientClass(ExpressionPointer endpoint, QuotientClassParts& out) {
        ExpressionPointer e = weakHeadNormalForm(environment_, endpoint);
        auto* a3 = std::get_if<Application>(&e->node);
        if (!a3) return false;
        auto* a2 = std::get_if<Application>(&a3->function->node);
        if (!a2) return false;
        auto* a1 = std::get_if<Application>(&a2->function->node);
        if (!a1) return false;
        auto* head = std::get_if<Constant>(&a1->function->node);
        if (!head || head->name != "Quotient.class_of") return false;
        out.rep = a3->argument;
        out.relation = a2->argument;
        out.carrier = a1->argument;
        out.level = head->universeArguments.empty()
            ? nullptr : head->universeArguments[0];
        return true;
    }

ExpressionPointer Elaborator::relaxClassEqualityToEquivalence(ExpressionPointer type) {
        ExpressionPointer equality = weakHeadNormalForm(environment_, type);
        auto* withRight = std::get_if<Application>(&equality->node);
        if (!withRight) return nullptr;
        ExpressionPointer rightEndpoint = withRight->argument;
        auto* withLeft = std::get_if<Application>(&withRight->function->node);
        if (!withLeft) return nullptr;
        ExpressionPointer leftEndpoint = withLeft->argument;
        auto* withCarrier = std::get_if<Application>(&withLeft->function->node);
        if (!withCarrier) return nullptr;
        auto* equalityHead = std::get_if<Constant>(&withCarrier->function->node);
        if (!equalityHead || equalityHead->name != "Equality") return nullptr;
        QuotientClassParts left, right;
        if (!peelQuotientClass(leftEndpoint, left)) return nullptr;
        if (!peelQuotientClass(rightEndpoint, right)) return nullptr;
        return makeApplication(makeApplication(left.relation, left.rep),
                                right.rep);
    }

ExpressionPointer Elaborator::tryQuotientSoundForClassEquality(
            const std::vector<LocalBinder>& localBinders,
            ExpressionPointer term,
            ExpressionPointer termTypeClosed,
            ExpressionPointer expectedTypeClosed) {
        if (!environment_.lookup("Quotient.equivalent_implies_equal")) return nullptr;
        Context openedContext = buildContextFromLocalBinders(localBinders);
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        EqualityComponents comps;
        try {
            comps = extractEqualityComponents(
                weakHeadNormalForm(environment_, expectedOpened),
                "quotient-sound coercion", 0);
        } catch (const ElaborateError&) {
            return nullptr;
        }
        QuotientClassParts left, right;
        if (!peelQuotientClass(comps.leftEndpoint, left)) return nullptr;
        if (!peelQuotientClass(comps.rightEndpoint, right)) return nullptr;
        if (!left.level) return nullptr;
        ExpressionPointer carrierLeft = left.carrier;
        ExpressionPointer relationLeft = left.relation;
        ExpressionPointer x = left.rep, y = right.rep;
        LevelPointer levelLeft = left.level;
        // The term must prove the equivalence `R(x, y)`.
        ExpressionPointer relationApplied = makeApplication(
            makeApplication(relationLeft, x), y);
        ExpressionPointer termTypeOpened = openOverLocalBinders(
            termTypeClosed, localBinders, localBinders.size());
        if (!isDefinitionallyEqual(environment_, openedContext,
                                   termTypeOpened, relationApplied)) {
            return nullptr;
        }
        // Build Quotient.equivalent_implies_equal.{u}(T, R, x, y, term); close the opened
        // endpoint pieces (term is already closed over the local binders).
        auto closeBack = [&](ExpressionPointer e) {
            return closeOverLocalBinders(e, localBinders, localBinders.size());
        };
        ExpressionPointer sound = makeConstant(
            "Quotient.equivalent_implies_equal", {levelLeft});
        sound = makeApplication(std::move(sound), closeBack(carrierLeft));
        sound = makeApplication(std::move(sound), closeBack(relationLeft));
        sound = makeApplication(std::move(sound), closeBack(x));
        sound = makeApplication(std::move(sound), closeBack(y));
        sound = makeApplication(std::move(sound), term);
        return sound;
    }

ExpressionPointer Elaborator::resolveEquivalenceInstance(
            ExpressionPointer carrierT, ExpressionPointer relationR,
            const std::vector<LocalBinder>& localBinders) {
        auto closeBack = [&](ExpressionPointer e) {
            return closeOverLocalBinders(e, localBinders, localBinders.size());
        };
        std::string carrierName = headConstantName(carrierT);
        auto entry = environment_.canonicalInstanceRegistry.find(
            std::make_tuple(std::string("IsEquivalenceRelation"), carrierName));
        if (entry != environment_.canonicalInstanceRegistry.end()
            && entry->second.universeParameters.empty()) {
            if (entry->second.parameterCount == 0) {
                return makeConstant(entry->second.termName, {});
            }
            // Open the leading parameter Pis as metavariables and solve them
            // against the actual (carrierT, relationR) by unifying components.
            std::set<std::string> parameterMetavariables;
            std::vector<std::string> parameterNames;
            ExpressionPointer openedType = entry->second.type;
            bool opened = true;
            for (int k = 0; k < entry->second.parameterCount; ++k) {
                auto* pi = std::get_if<Pi>(&openedType->node);
                if (!pi) { opened = false; break; }
                std::string fresh = "_eqInstanceParameter_" + std::to_string(k)
                    + "_" + entry->second.termName;
                parameterMetavariables.insert(fresh);
                parameterNames.push_back(fresh);
                openedType = openBinder(pi->codomain, fresh,
                                         FreeVariableOrigin::Internal);
            }
            auto* outer = opened
                ? std::get_if<Application>(&openedType->node) : nullptr;
            auto* inner = outer
                ? std::get_if<Application>(&outer->function->node) : nullptr;
            if (inner) {
                std::map<std::string, ExpressionPointer> assignment;
                unifyConstructorParameters(inner->argument, carrierT,
                                            parameterMetavariables, assignment);
                unifyConstructorParameters(outer->argument, relationR,
                                            parameterMetavariables, assignment);
                bool allSolved = true;
                for (const auto& name : parameterNames)
                    if (!assignment.count(name)) { allSolved = false; break; }
                if (allSolved) {
                    ExpressionPointer instanceTerm =
                        makeConstant(entry->second.termName, {});
                    for (const auto& name : parameterNames)
                        instanceTerm = makeApplication(std::move(instanceTerm),
                                                        assignment[name]);
                    return closeBack(instanceTerm);
                }
            }
        }
        // Fallback: a LOCAL hypothesis already proves
        // `IsEquivalenceRelation(carrierT, relationR)` (the registry can't hold
        // it — e.g. `Group.SameCoset`'s equivalence needs a subgroup witness).
        Context openedContext = buildContextFromLocalBinders(localBinders);
        int N = static_cast<int>(localBinders.size());
        for (int b = N - 1; b >= 0; --b) {
            ExpressionPointer hyp = weakHeadNormalForm(environment_,
                openOverLocalBinders(
                    liftBoundVariables(localBinders[b].type, N - b, 0),
                    localBinders, localBinders.size()));
            auto* outer = std::get_if<Application>(&hyp->node);
            if (!outer) continue;
            auto* inner = std::get_if<Application>(&outer->function->node);
            if (!inner) continue;
            auto* head = std::get_if<Constant>(&inner->function->node);
            if (!head || head->name != "IsEquivalenceRelation") continue;
            if (isDefinitionallyEqual(environment_, openedContext,
                                       inner->argument, carrierT)
                && isDefinitionallyEqual(environment_, openedContext,
                                          outer->argument, relationR)) {
                return makeBoundVariable(N - 1 - b);
            }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryQuotientExactBridge(
            ExpressionPointer goalClosed,
            const std::vector<LocalBinder>& localBinders) {
        if (!environment_.lookup("Quotient.equal_implies_equivalent")) return nullptr;
        Context openedContext = buildContextFromLocalBinders(localBinders);
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        ExpressionPointer goalWhnf =
            weakHeadNormalForm(environment_, goalOpened);
        // Cheap gate: the goal must at least be an application (R applied).
        if (!std::get_if<Application>(&goalWhnf->node)) return nullptr;

        // Scan LOCAL hypotheses only for an `mk a = mk b` equality (cheap;
        // the expensive library-equality scan in collectContextEqualities is
        // pointless here — class equalities are local facts). Mirrors the
        // local-binder loop in collectContextEqualities.
        // Peel `Equality(T, lhs, rhs)` with a head check — NO exceptions
        // (this runs per-binder on most goals; a throwing extractor here is a
        // measurable hot-loop cost).
        auto peelEquality = [&](ExpressionPointer hyp,
                                ExpressionPointer& lhs,
                                ExpressionPointer& rhs) -> bool {
            ExpressionPointer e = weakHeadNormalForm(environment_, hyp);
            auto* a3 = std::get_if<Application>(&e->node);
            if (!a3) return false;
            rhs = a3->argument;
            auto* a2 = std::get_if<Application>(&a3->function->node);
            if (!a2) return false;
            lhs = a2->argument;
            auto* a1 = std::get_if<Application>(&a2->function->node);
            if (!a1) return false;
            auto* head = std::get_if<Constant>(&a1->function->node);
            return head && head->name == "Equality";
        };

        // Local facts — binders AND conjunction legs (shared
        // `collectLocalBinderFacts`) — so a class equality buried in an
        // `… ∧ (mk a = mk b)` hypothesis coerces like a stand-alone one.
        for (const ContextFact& fact : collectLocalBinderFacts(localBinders)) {
            ExpressionPointer eqLhs, eqRhs;
            if (!peelEquality(fact.type, eqLhs, eqRhs)) continue;
            ExpressionPointer proofExpr = fact.proofTerm;
            QuotientClassParts left, right;
            if (!peelQuotientClass(openOverLocalBinders(eqLhs, localBinders,
                                       localBinders.size()), left)) continue;
            if (!peelQuotientClass(openOverLocalBinders(eqRhs, localBinders,
                                       localBinders.size()), right)) continue;
            if (!left.level) continue;
            ExpressionPointer carrierL = left.carrier, relationL = left.relation;
            ExpressionPointer repA = left.rep, repB = right.rep;
            LevelPointer levelL = left.level;
            if (!isDefinitionallyEqual(environment_, openedContext,
                                       carrierL, right.carrier)) continue;
            if (!isDefinitionallyEqual(environment_, openedContext,
                                       relationL, right.relation)) continue;
            // The goal must be exactly `R(a, b)` for these reps.
            ExpressionPointer relationApplied = makeApplication(
                makeApplication(relationL, repA), repB);
            if (!isDefinitionallyEqual(environment_, openedContext,
                                       goalWhnf, relationApplied)) continue;
            // Resolve the carrier's IsEquivalenceRelation instance (solving
            // any relation/carrier parameters, e.g. CongruentModulo(m)).
            // Resolve the equivalence — a registered instance (param-free or
            // parameterized) or a local IsEquivalenceRelation hypothesis. The
            // resolver returns it already closed over the local binders.
            ExpressionPointer equivalenceInstance =
                resolveEquivalenceInstance(carrierL, relationL, localBinders);
            if (!equivalenceInstance) continue;
            auto closeBack = [&](ExpressionPointer e) {
                return closeOverLocalBinders(e, localBinders,
                                              localBinders.size());
            };
            ExpressionPointer exact = makeConstant("Quotient.equal_implies_equivalent", {levelL});
            exact = makeApplication(std::move(exact), closeBack(carrierL));
            exact = makeApplication(std::move(exact), closeBack(relationL));
            exact = makeApplication(std::move(exact), equivalenceInstance);
            exact = makeApplication(std::move(exact), closeBack(repA));
            exact = makeApplication(std::move(exact), closeBack(repB));
            exact = makeApplication(std::move(exact), proofExpr);
            // Validate the assembled term proves the goal before returning.
            try {
                ExpressionPointer inferred = inferType(
                    environment_, openedContext,
                    openOverLocalBinders(exact, localBinders,
                                          localBinders.size()));
                if (isDefinitionallyEqual(environment_, openedContext,
                                          inferred, goalWhnf)) {
                    return exact;
                }
            } catch (const TypeError&) {
                // Assembled term didn't type-check (e.g. wrong instance);
                // try the next equality.
            }
        }
        return nullptr;
    }


// Out-of-line Elaborator method definitions: lemma-index lookup + diff classification used by the auto-prover
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::instantiateLemmaBinders(
        ExpressionPointer expression,
        const std::vector<ExpressionPointer>& bindings,
        int nestedBinderDepth) {
        int N = static_cast<int>(bindings.size());
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            if (bv->deBruijnIndex < nestedBinderDepth) {
                return expression;
            }
            int relative = bv->deBruijnIndex - nestedBinderDepth;
            if (relative < N) {
                return liftBoundVariables(bindings[relative],
                                            nestedBinderDepth, 0);
            }
            // A reference past the lemma's own binders. Library
            // rewrite lemmas shouldn't produce one, but if they do,
            // close the gap left by the eliminated lemma binders.
            return makeBoundVariable(
                bv->deBruijnIndex - N);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return makeApplication(
                instantiateLemmaBinders(application->function,
                                          bindings, nestedBinderDepth),
                instantiateLemmaBinders(application->argument,
                                          bindings, nestedBinderDepth));
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                instantiateLemmaBinders(pi->domain, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(pi->codomain, bindings,
                                          nestedBinderDepth + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                instantiateLemmaBinders(lambda->domain, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(lambda->body, bindings,
                                          nestedBinderDepth + 1));
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return makeLet(let->displayHint,
                instantiateLemmaBinders(let->type, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(let->value, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(let->body, bindings,
                                          nestedBinderDepth + 1));
        }
        return expression;
    }

ExpressionPointer Elaborator::tryLemmaIndexLookup(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer subLeft,
        ExpressionPointer subRight) {
        // We look up two buckets: the subLeft-keyed bucket, and the
        // wildcard bucket. The wildcard bucket holds reverse-direction
        // entries for lemmas whose RHS is a bare metavariable (e.g.
        // the identity `(x : T) → op(x, unit) = x`, which we want to
        // fire when subLeft is `x` and subRight is `op(x, unit)`). The
        // forward-direction entry of those lemmas, indexed under their
        // op-headed LHS, lands in the regular bucket as usual.
        std::vector<uint64_t> keys;
        keys.push_back(spineHash(subLeft));
        ExpressionPointer wildcardProbe = makeBoundVariable(0);
        uint64_t wildcardKey = spineHash(wildcardProbe);
        if (wildcardKey != keys[0]) {
            keys.push_back(wildcardKey);
        }
        for (uint64_t key : keys) {
        auto range = lemmaIndex_.equal_range(key);
        for (auto iterator = range.first;
             iterator != range.second; ++iterator) {
            const RewriteLemma& lemma = iterator->second;
            std::vector<ExpressionPointer> bindings(lemma.binderCount);
            ExpressionPointer patternFor = lemma.reverseDirection
                ? lemma.rhs : lemma.lhs;
            ExpressionPointer otherSide = lemma.reverseDirection
                ? lemma.lhs : lemma.rhs;
            if (!matchAgainstPattern(patternFor, subLeft,
                                       lemma.binderCount, bindings)) {
                continue;
            }
            // Symmetric pass: also match `otherSide` against
            // `subRight` so the lemma's binders get filled from
            // WHICHEVER side carries them. Without this, a lemma
            // stated `-x + x = 0` would fire on `-1 + 1 = 0` (the
            // matched LHS binds x) but NOT on `0 = -1 + 1` (the
            // matched RHS is bare, leaving x unbound). matchAgainst-
            // Pattern's set-or-check logic also doubles as the
            // consistency check that used to live in the
            // `structurallyEqual(expectedOther, subRight)` line
            // below — when bindings overlap between the two sides,
            // re-binding the same slot to the same subterm succeeds,
            // and a conflict between the two sides correctly rejects
            // the lemma.
            if (!matchAgainstPattern(otherSide, subRight,
                                       lemma.binderCount, bindings)) {
                continue;
            }
            // Discharge unbound preconditions outer-to-inner: a binder
            // type at conclusion-frame index i may reference outer
            // binders (index > i), so we need those filled first.
            // Pattern matching populates LHS/RHS slots; this pass
            // populates propositional preconditions by searching local
            // hypotheses for proofs of the instantiated type. Lemmas
            // like `padic_valuation_multiplicative(prime, a, b)
            // (primality)(aPos)(bPos)` have primality/aPos/bPos in
            // scope via the user's `claim`s — the discharge finds them
            // and the lemma fires without an explicit `by`.
            bool dischargedAll = true;
            if (static_cast<int>(lemma.binderTypes.size())
                == lemma.binderCount) {
                Context openedContext =
                    buildContextFromLocalBinders(localBinders);
                for (int i = lemma.binderCount - 1; i >= 0; --i) {
                    if (bindings[i]) continue;
                    if (!binderReferencesAllBound(
                            lemma.binderTypes[i], bindings)) {
                        dischargedAll = false;
                        break;
                    }
                    ExpressionPointer slotType = instantiateLemmaBinders(
                        lemma.binderTypes[i], bindings);
                    ExpressionPointer slotTypeOpened =
                        openOverLocalBinders(slotType, localBinders,
                                              localBinders.size());
                    ExpressionPointer slotTypeNormalised;
                    try {
                        slotTypeNormalised = weakHeadNormalForm(
                            environment_, slotTypeOpened);
                    } catch (const TypeError&) {
                        dischargedAll = false;
                        break;
                    }
                    bool found = false;
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
                        } catch (const TypeError&) {
                            eq = false;
                        }
                        if (eq) {
                            int deBruijnIndex =
                                static_cast<int>(localBinders.size())
                                - 1 - j;
                            bindings[i] =
                                makeBoundVariable(deBruijnIndex);
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        dischargedAll = false;
                        break;
                    }
                }
            } else {
                // Older registration without binderTypes; fall back to
                // the original all-or-nothing check.
                dischargedAll = false;
                for (const auto& binding : bindings) {
                    if (!binding) { dischargedAll = false; break; }
                    dischargedAll = true;
                }
            }
            if (!dischargedAll) continue;
            bool allBound = true;
            for (const auto& binding : bindings) {
                if (!binding) { allBound = false; break; }
            }
            if (!allBound) continue;
            // The two `matchAgainstPattern` calls above already
            // enforced `otherSide[bindings] = subRight` structurally,
            // so the redundant re-check that used to live here is
            // gone. (Propositional preconditions filled by the
            // discharge pass don't appear in `otherSide` — they're
            // referenced from binder types, not from the conclusion's
            // LHS/RHS — so they don't change the check's outcome.)
            // Assemble the lemma application: `lemmaName(binding_for_BV(n-1),
            // …, binding_for_BV(0))` — outer binder first since that's
            // the order of the Π chain.
            ExpressionPointer call =
                makeConstant(lemma.lemmaName, {});
            for (int i = lemma.binderCount - 1; i >= 0; --i) {
                call = makeApplication(std::move(call), bindings[i]);
            }
            if (!lemma.reverseDirection) {
                return call;
            }
            // Reverse direction: lemma proves `RHS = LHS` but the diff
            // wants `subLeft = subRight` where subLeft matches the
            // lemma's RHS. So the lemma instance proves
            // `subRight = subLeft`, which we wrap with
            // `Equality.symmetry` to get the desired direction.
            ExpressionPointer carrierClosed;
            LevelPointer carrierLevelAtThisLevel;
            try {
                // inferTypeInLocalContext returns the type in OPENED form
                // (Internal free variables for the local binders). The
                // symmetry term we splice it into is in CLOSED (de Bruijn)
                // form, so the carrier MUST be closed too — otherwise an
                // abstract carrier like `Group.carrier(H)` leaks an
                // unbound internal `H` that the kernel later rejects.
                carrierClosed = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, subLeft),
                    localBinders, localBinders.size());
                carrierLevelAtThisLevel = typeUniverseOf(
                    localBinders, subLeft);
            } catch (const TypeError&) {
                continue;
            } catch (const ElaborateError&) {
                continue;
            }
            ExpressionPointer symmetryCall = makeConstant(
                "Equality.symmetry", {carrierLevelAtThisLevel});
            symmetryCall = makeApplication(
                std::move(symmetryCall), carrierClosed);
            symmetryCall = makeApplication(
                std::move(symmetryCall), subRight);
            symmetryCall = makeApplication(
                std::move(symmetryCall), subLeft);
            symmetryCall = makeApplication(
                std::move(symmetryCall), std::move(call));
            return symmetryCall;
        }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryClassifyDiff(
        const std::vector<LocalBinder>& localBinders,
        const Context& openedContext,
        ExpressionPointer subLeft,
        ExpressionPointer subRight) {
        if (ExpressionPointer proof = tryLemmaIndexLookup(
                localBinders, subLeft, subRight)) {
            return proof;
        }
        // Local hypothesis match (forward and symmetric). Scan
        // local binders for one whose type is
        // Equality(_, subLeft, subRight) or
        // Equality(_, subRight, subLeft).
        {
            ExpressionPointer subLeftOpened = openOverLocalBinders(
                subLeft, localBinders, localBinders.size());
            ExpressionPointer subRightOpened = openOverLocalBinders(
                subRight, localBinders, localBinders.size());
            for (int i =
                     static_cast<int>(localBinders.size()) - 1;
                 i >= 0; --i) {
                ExpressionPointer binderTypeOpened = openOverLocalBinders(
                    localBinders[i].type, localBinders, i);
                ExpressionPointer normalized = weakHeadNormalForm(
                    environment_, binderTypeOpened);
                // Expect App(App(App(Equality, carrier), x), y).
                auto* app3 =
                    std::get_if<Application>(&normalized->node);
                if (!app3) continue;
                auto* app2 =
                    std::get_if<Application>(&app3->function->node);
                if (!app2) continue;
                auto* app1 =
                    std::get_if<Application>(&app2->function->node);
                if (!app1) continue;
                auto* head =
                    std::get_if<Constant>(&app1->function->node);
                if (!head || head->name != "Equality") continue;
                ExpressionPointer eqLeft = app2->argument;
                ExpressionPointer eqRight = app3->argument;
                int deBruijnIndex =
                    static_cast<int>(localBinders.size()) - 1 - i;
                if (isDefinitionallyEqual(environment_,
                        openedContext, eqLeft, subLeftOpened)
                    && isDefinitionallyEqual(environment_,
                        openedContext, eqRight, subRightOpened)) {
                    return makeBoundVariable(deBruijnIndex);
                }
                if (isDefinitionallyEqual(environment_,
                        openedContext, eqLeft, subRightOpened)
                    && isDefinitionallyEqual(environment_,
                        openedContext, eqRight, subLeftOpened)) {
                    // Wrap with Equality.symmetry.
                    auto* carrierConst =
                        std::get_if<Constant>(&app1->argument->node);
                    (void)carrierConst;
                    ExpressionPointer carrierAtThisLevel =
                        app1->argument;
                    LevelPointer carrierLevelAtThisLevel;
                    if (!head->universeArguments.empty()) {
                        carrierLevelAtThisLevel =
                            head->universeArguments[0];
                    } else {
                        // Should not happen: Equality is universe-
                        // polymorphic and always has a level arg.
                        return nullptr;
                    }
                    ExpressionPointer carrierClosed =
                        closeOverLocalBinders(
                            carrierAtThisLevel, localBinders,
                            localBinders.size());
                    ExpressionPointer hypBoundVar =
                        makeBoundVariable(deBruijnIndex);
                    ExpressionPointer symmetryCall = makeConstant(
                        "Equality.symmetry",
                        {carrierLevelAtThisLevel});
                    symmetryCall = makeApplication(
                        std::move(symmetryCall), carrierClosed);
                    symmetryCall = makeApplication(
                        std::move(symmetryCall), subRight);
                    symmetryCall = makeApplication(
                        std::move(symmetryCall), subLeft);
                    symmetryCall = makeApplication(
                        std::move(symmetryCall),
                        std::move(hypBoundVar));
                    return symmetryCall;
                }
            }
        }
        return nullptr;
    }


// Out-of-line Elaborator method definitions: desugaring of eliminator/intro forms: absurd, overload resolution, or/exists-eliminate, quotient sound/lift/induct, congruenceOf
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::desugarAbsurd(
        SurfaceExpressionPointer witnessSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "absurd at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "absurd needs an expected type from context — use it "
                "in a position with a known goal");
        }

        ExpressionPointer witnessKernel =
            elaborateExpression(*witnessSurface, localBinders);
        ExpressionPointer witnessTypeOpened = weakHeadNormalForm(
            environment_,
            inferTypeInLocalContext(localBinders, witnessKernel));
        ExpressionPointer witnessType = closeOverLocalBinders(
            witnessTypeOpened, localBinders, localBinders.size());

        ExpressionPointer falseProof;

        // Shape: witness is already a proof of False.
        if (auto* constant =
                std::get_if<Constant>(&witnessType->node)) {
            if (constant->name == "False") {
                falseProof = witnessKernel;
            }
        }

        // Shape: `LessOrEqual(successor(K), zero)`. The type is built
        // as `App(App(LessOrEqual, successor(K)), zero)`. Both
        // endpoints are WHNF'd so that definitional reductions like
        // `successor(k) + b → successor(k + b)` expose the
        // constructor.
        if (!falseProof) {
            auto* outerApp =
                std::get_if<Application>(&witnessType->node);
            if (outerApp) {
                ExpressionPointer rhsNormalised = weakHeadNormalForm(
                    environment_, outerApp->argument);
                auto* zeroConstant = std::get_if<Constant>(
                    &rhsNormalised->node);
                bool rhsIsZero = zeroConstant
                    && zeroConstant->name == "zero";
                auto* innerApp = std::get_if<Application>(
                    &outerApp->function->node);
                if (rhsIsZero && innerApp) {
                    auto* head = std::get_if<Constant>(
                        &innerApp->function->node);
                    if (head && head->name == "LessOrEqual") {
                        ExpressionPointer lhsNormalised =
                            weakHeadNormalForm(
                                environment_, innerApp->argument);
                        auto* succApp = std::get_if<Application>(
                            &lhsNormalised->node);
                        if (succApp) {
                            auto* succHead = std::get_if<Constant>(
                                &succApp->function->node);
                            if (succHead
                                && succHead->name == "successor") {
                                ExpressionPointer kValue =
                                    succApp->argument;
                                ExpressionPointer call = makeConstant(
                                    "Natural.not_less_or_equal_successor_zero",
                                    {});
                                call = makeApplication(
                                    std::move(call), kValue);
                                call = makeApplication(
                                    std::move(call), witnessKernel);
                                falseProof = std::move(call);
                            }
                        }
                    }
                }
            }
        }

        // Shapes: `successor(K) = zero` or `zero = successor(K)` on
        // `Natural`. We extract via extractEqualityComponents and
        // dispatch based on which side is `successor(_)`.
        if (!falseProof) {
            EqualityComponents components;
            bool hasComponents = false;
            try {
                components = extractEqualityComponents(
                    witnessType, "absurd", line);
                hasComponents = true;
            } catch (const ElaborateError&) {
                hasComponents = false;
            }
            if (hasComponents) {
                auto* carrierConstant = std::get_if<Constant>(
                    &components.carrierType->node);
                bool carrierIsNatural = carrierConstant
                    && carrierConstant->name == "Natural";
                auto isSuccessor = [&](ExpressionPointer expression,
                                       ExpressionPointer& inner)
                                       -> bool {
                    ExpressionPointer normalised =
                        weakHeadNormalForm(environment_, expression);
                    auto* application = std::get_if<Application>(
                        &normalised->node);
                    if (!application) return false;
                    auto* head = std::get_if<Constant>(
                        &application->function->node);
                    if (!head || head->name != "successor") {
                        return false;
                    }
                    inner = application->argument;
                    return true;
                };
                auto isZero = [&](ExpressionPointer expression)
                                  -> bool {
                    ExpressionPointer normalised =
                        weakHeadNormalForm(environment_, expression);
                    auto* constant = std::get_if<Constant>(
                        &normalised->node);
                    return constant && constant->name == "zero";
                };
                ExpressionPointer kValue;
                if (carrierIsNatural
                    && isSuccessor(components.leftEndpoint, kValue)
                    && isZero(components.rightEndpoint)) {
                    ExpressionPointer call = makeConstant(
                        "Natural.successor_not_zero", {});
                    call = makeApplication(std::move(call), kValue);
                    call = makeApplication(std::move(call),
                                            witnessKernel);
                    falseProof = std::move(call);
                } else if (carrierIsNatural
                    && isZero(components.leftEndpoint)
                    && isSuccessor(components.rightEndpoint,
                                    kValue)) {
                    ExpressionPointer call = makeConstant(
                        "Natural.zero_not_successor", {});
                    call = makeApplication(std::move(call), kValue);
                    call = makeApplication(std::move(call),
                                            witnessKernel);
                    falseProof = std::move(call);
                }
            }
        }

        if (!falseProof) {
            throwElaborate(
                "absurd: argument's type is not `False` and doesn't "
                "match a recognized contradiction shape "
                "(supported: succ(K) ≤ zero, succ(K) = zero, "
                "zero = succ(K)). Use `False.eliminate_proposition` "
                "directly if you already have a False proof from "
                "some other source.");
        }

        // Dispatch between `False.eliminate_proposition` (for goals in
        // Proposition) and `False.eliminate.{u}` (for goals in
        // Type u = Sort u+1). The goal's universe level is the level
        // of the Sort returned by inferType(expectedType).
        Context openedContext = buildContextFromLocalBinders(localBinders);
        ExpressionPointer goalSort = weakHeadNormalForm(
            environment_,
            inferType(environment_, openedContext,
                       openOverLocalBinders(
                           expectedType, localBinders,
                           localBinders.size())));
        auto* sortNode = std::get_if<Sort>(&goalSort->node);
        if (!sortNode) {
            throwElaborate(
                "absurd: internal — goal type's kind isn't a Sort");
        }
        std::optional<int> levelConstant =
            levelAsConstant(sortNode->level);

        if (levelConstant && *levelConstant == 0) {
            ExpressionPointer call = makeConstant(
                "False.eliminate_proposition", {});
            call = makeApplication(std::move(call), expectedType);
            call = makeApplication(std::move(call),
                                    std::move(falseProof));
            return call;
        }
        if (!levelConstant) {
            throwElaborate(
                "absurd: goal's universe isn't a concrete level — "
                "v1 only dispatches against Proposition or "
                "Type N for explicit N");
        }
        // Type N case: pass N as the universe arg to False.eliminate.
        ExpressionPointer call = makeConstant(
            "False.eliminate",
            {makeLevelConst(*levelConstant - 1)});
        call = makeApplication(std::move(call), expectedType);
        call = makeApplication(std::move(call), std::move(falseProof));
        return call;
    }

ExpressionPointer Elaborator::resolveOverloadedCall(
        const std::string& aliasName,
        const std::vector<std::string>& candidateNames,
        const std::vector<SurfaceExpressionPointer>& argumentSurfaces,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "overload '" + aliasName + "' resolution at line "
            + std::to_string(line));
        // Elaborate arguments and infer their head-type names.
        // When the argument surface is a SurfaceAscription
        // `(expr : T)`, derive the head name from T directly rather
        // than from inferType on the elaborated kernel term. The
        // ascription is the user's explicit label, and inferType
        // unfolds carrier aliases (e.g. `Real` -> `Quotient(...)`),
        // which would lose the label needed to pick the carrier-
        // specific overload. Concretely: `abs((Quotient.mk(rep) :
        // Real))` would otherwise match the Quotient head (no
        // candidate) instead of Real.
        std::vector<ExpressionPointer> argumentKernels;
        std::vector<std::string> argumentTypeNames;
        for (const auto& argumentSurface : argumentSurfaces) {
            ExpressionPointer argumentKernel =
                elaborateExpression(*argumentSurface, localBinders);
            argumentKernels.push_back(argumentKernel);
            std::string typeName;
            if (auto* ascription = std::get_if<SurfaceAscription>(
                    &argumentSurface->node)) {
                ExpressionPointer ascribedType = elaborateExpression(
                    *ascription->type, localBinders);
                typeName = headConstantName(ascribedType);
            } else {
                ExpressionPointer argumentTypeRaw =
                    inferTypeInLocalContext(localBinders, argumentKernel);
                typeName = headConstantName(argumentTypeRaw);
            }
            argumentTypeNames.push_back(std::move(typeName));
        }
        // Find candidates whose first N parameter-type names match.
        std::vector<std::string> matches;
        for (const auto& candidateName : candidateNames) {
            const Declaration* declaration =
                environment_.lookup(candidateName);
            if (!declaration) continue;
            ExpressionPointer signature = declarationType(*declaration);
            if (!signatureAcceptsArgumentTypes(signature,
                                                  argumentTypeNames)) {
                continue;
            }
            matches.push_back(candidateName);
        }
        if (matches.empty()) {
            std::string message =
                "no overload of '" + aliasName + "' matches arguments "
                "of types (";
            for (size_t i = 0; i < argumentTypeNames.size(); ++i) {
                if (i > 0) message += ", ";
                message += argumentTypeNames[i];
            }
            message += "); candidates:";
            for (const auto& candidate : candidateNames) {
                message += "\n  " + candidate;
            }
            throwElaborate(message);
        }
        if (matches.size() > 1) {
            std::string message =
                "ambiguous overload of '" + aliasName
                + "' on argument types (";
            for (size_t i = 0; i < argumentTypeNames.size(); ++i) {
                if (i > 0) message += ", ";
                message += argumentTypeNames[i];
            }
            message += "); multiple candidates match:";
            for (const auto& match : matches) {
                message += "\n  " + match;
            }
            message += "\nuse the fully-qualified name to disambiguate";
            throwElaborate(message);
        }
        // Build a SurfaceApplication of the chosen candidate and
        // re-elaborate it — that reuses universe-inference, leading-
        // argument inference, etc.
        SurfaceExpressionPointer resolvedHead = makeSurfaceIdentifier(
            matches[0], /*universeArgs=*/{}, line, column);
        SurfaceExpressionPointer resolvedCall = makeSurfaceApplication(
            std::move(resolvedHead),
            argumentSurfaces,
            line, column);
        return elaborateExpression(*resolvedCall, localBinders,
                                     expectedType);
    }

bool Elaborator::structureHeadIsClass(const std::string& name) {
        const Declaration* decl = environment_.lookup(name);
        if (!decl) return false;
        ExpressionPointer type = declarationType(*decl);
        if (!type) return false;
        auto* firstPi = std::get_if<Pi>(&type->node);
        if (!firstPi) return false;
        if (!std::get_if<Sort>(&firstPi->domain->node)) return false;
        ExpressionPointer cursor = type;
        while (auto* pi = std::get_if<Pi>(&cursor->node)) {
            cursor = pi->codomain;
        }
        auto* sort = std::get_if<Sort>(&cursor->node);
        if (!sort) return false;
        auto* level = std::get_if<LevelConst>(&sort->level->node);
        return level != nullptr && level->value == 0;
    }

std::string Elaborator::headConstantName(ExpressionPointer typeExpression) {
        ExpressionPointer cursor = typeExpression;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            cursor = application->function;
        }
        if (auto* constant = std::get_if<Constant>(&cursor->node)) {
            return constant->name;
        }
        ExpressionPointer reduced = weakHeadNormalForm(
            environment_, typeExpression);
        while (auto* application =
                   std::get_if<Application>(&reduced->node)) {
            reduced = weakHeadNormalForm(environment_,
                                          application->function);
        }
        if (auto* constant = std::get_if<Constant>(&reduced->node)) {
            return constant->name;
        }
        return "<unknown>";
    }

ExpressionPointer Elaborator::carrierProjectionField(ExpressionPointer type) {
        auto* application = std::get_if<Application>(&type->node);
        if (!application) return nullptr;
        auto* projector =
            std::get_if<Constant>(&application->function->node);
        if (!projector) return nullptr;
        if (projector->name != "Ring.carrier"
            && projector->name != "CommutativeRing.carrier") {
            return nullptr;
        }
        ExpressionPointer bundle = weakHeadNormalForm(
            environment_, application->argument);
        std::vector<ExpressionPointer> arguments;
        ExpressionPointer cursor = bundle;
        while (auto* inner = std::get_if<Application>(&cursor->node)) {
            arguments.push_back(inner->argument);
            cursor = inner->function;
        }
        auto* constructor = std::get_if<Constant>(&cursor->node);
        if (!constructor) return nullptr;
        if (constructor->name != "Ring.make"
            && constructor->name != "CommutativeRing.make") {
            return nullptr;
        }
        if (arguments.empty()) return nullptr;
        return arguments.back();  // first constructor arg = the carrier
    }

bool Elaborator::signatureAcceptsArgumentTypes(
        ExpressionPointer signature,
        const std::vector<std::string>& argumentTypeNames) {
        ExpressionPointer cursor = signature;
        for (const auto& expectedName : argumentTypeNames) {
            cursor = weakHeadNormalForm(environment_, cursor);
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) return false;
            std::string actualName = headConstantName(pi->domain);
            if (actualName != expectedName) return false;
            cursor = pi->codomain;
        }
        return true;
    }

bool Elaborator::tryDecomposeQuotient(
        ExpressionPointer typeExpression,
        QuotientDecomposition& result) {
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, typeExpression);
        auto* outerApp = std::get_if<Application>(&cursor->node);
        if (!outerApp) return false;
        auto* innerApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!innerApp) return false;
        auto* quotientConstant =
            std::get_if<Constant>(&innerApp->function->node);
        if (!quotientConstant || quotientConstant->name != "Quotient")
            return false;
        if (quotientConstant->universeArguments.size() != 1)
            return false;
        result.carrierType = innerApp->argument;
        result.relation = outerApp->argument;
        result.universeLevel = quotientConstant->universeArguments[0];
        return true;
    }

ExpressionPointer Elaborator::desugarQuotientMk(
        SurfaceExpressionPointer representativeSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.mk(rep) at line " + std::to_string(line));
        ExpressionPointer representativeKernel =
            elaborateExpression(*representativeSurface, localBinders);
        ExpressionPointer representativeTypeOpened =
            inferTypeInLocalContext(localBinders, representativeKernel);
        ExpressionPointer representativeType = closeOverLocalBinders(
            representativeTypeOpened, localBinders, localBinders.size());
        LevelPointer universeLevel =
            typeUniverseOf(localBinders, representativeKernel);

        ExpressionPointer relation;
        if (expectedType) {
            QuotientDecomposition decomp;
            if (tryDecomposeQuotient(expectedType, decomp)) {
                relation = decomp.relation;
            }
        }
        if (!relation) {
            throwElaborate(
                "Quotient.mk(rep): cannot infer the equivalence "
                "relation `R`. The short form needs an expected type "
                "of shape `Quotient(T, R)` from context. Common spots "
                "this fails: operand of unary `-`, immediate body of "
                "`function (rep) =>` inside `Quotient.lift`, or any "
                "position with no propagated expected type. Fall back "
                "to the explicit 3-arg form: `Quotient.mk(T, R, rep)`. "
                "Needed an expected type of the form "
                "`Quotient(T, R)` in context");
        }
        ExpressionPointer call = makeConstant(
            "Quotient.mk", {universeLevel});
        call = makeApplication(std::move(call), representativeType);
        call = makeApplication(std::move(call), relation);
        call = makeApplication(std::move(call),
                                std::move(representativeKernel));
        return call;
    }

ExpressionPointer Elaborator::desugarQuotientSound(
        SurfaceExpressionPointer xSurface,
        SurfaceExpressionPointer ySurface,
        SurfaceExpressionPointer proofSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.sound at line " + std::to_string(line));
        // Prefer pulling `T` and `R` from the expected type. Its
        // shape (after WHNF/δ-reduction) is
        // `Equality(Quotient(T, R), mk(T, R, x), mk(T, R, y))`, which
        // pins down `R` as the user wrote it — important when `R`
        // δ-reduces (`IntegerEquivalent → λ rep1 rep2. (...)`) and we'd
        // otherwise infer the reduced form from the proof's type.
        ExpressionPointer carrierType;
        ExpressionPointer relation;
        LevelPointer universeLevel;
        if (expectedType) {
            ExpressionPointer expectedOpened = weakHeadNormalForm(
                environment_, expectedType);
            // Expect Equality(Q, ..., ...) → extract Q.
            if (auto* eqOuter =
                    std::get_if<Application>(&expectedOpened->node)) {
                if (auto* eqMid =
                        std::get_if<Application>(
                            &eqOuter->function->node)) {
                    if (auto* eqInner =
                            std::get_if<Application>(
                                &eqMid->function->node)) {
                        QuotientDecomposition decomp;
                        if (tryDecomposeQuotient(eqInner->argument, decomp)) {
                            // `decomp.*` are sub-expressions of
                            // `expectedType`, which is already in
                            // closed-over-localBinders form — use them
                            // directly (as `desugarQuotientMk` does).
                            // Re-closing here would shift any
                            // BoundVariable the relation carries (e.g. the
                            // `modulus` of a parameterized quotient
                            // `IntegerMod(modulus)`), leaking a dangling
                            // index. Non-parameterized relations are bare
                            // constants, so the old extra close was a
                            // silent no-op for them.
                            carrierType = decomp.carrierType;
                            relation = decomp.relation;
                            universeLevel = decomp.universeLevel;
                        }
                    }
                }
            }
        }

        ExpressionPointer xKernel = elaborateExpression(
            *xSurface, localBinders);
        ExpressionPointer yKernel = elaborateExpression(
            *ySurface, localBinders);
        // When the relation is already pinned (from the expected type),
        // elaborate the proof against `R(x, y)` so a user-written lambda
        // respect proof (e.g. `function (epsilon) => …` for a sequence-
        // equivalence relation) receives the relation's codomain as its
        // body's expected type — no `({ … } : …)` ascription needed. When
        // R is not yet known (the no-expected-type case, where R is
        // recovered FROM the proof's type below), pass no expected type.
        ExpressionPointer proofExpectedType =
            relation
                ? makeApplication(
                      makeApplication(relation, xKernel), yKernel)
                : nullptr;
        ExpressionPointer proofKernel = elaborateExpression(
            *proofSurface, localBinders, proofExpectedType);

        if (!carrierType) {
            ExpressionPointer xTypeOpened =
                inferTypeInLocalContext(localBinders, xKernel);
            carrierType = closeOverLocalBinders(
                xTypeOpened, localBinders, localBinders.size());
            universeLevel = typeUniverseOf(localBinders, xKernel);
        }
        if (!relation) {
            // Fallback: pull `R` from proof's type as `R(x, y)`. Try the
            // proof's type AS WRITTEN first — `R` already appears applied
            // to its two arguments, so `inner->function` is exactly the
            // relation. Only WHNF as a secondary attempt. WHNF-ing first
            // would over-unfold a Definition-headed relation (e.g.
            // `Integer.CongruentModulo(modulus)` → `Integer.divides` →
            // the underlying `Exists`), recovering the wrong head — which
            // is what breaks short `Quotient.sound` inside a short
            // `Quotient.lift` respect handler, where no expected type is
            // propagated to pin `R`.
            ExpressionPointer proofTypeOpened =
                inferTypeInLocalContext(localBinders, proofKernel);
            auto extractRelation =
                [&](ExpressionPointer proofType) -> ExpressionPointer {
                if (auto* outer = std::get_if<Application>(
                        &proofType->node)) {
                    if (auto* inner = std::get_if<Application>(
                            &outer->function->node)) {
                        return closeOverLocalBinders(
                            inner->function, localBinders,
                            localBinders.size());
                    }
                }
                return nullptr;
            };
            relation = extractRelation(proofTypeOpened);
            if (!relation) {
                relation = extractRelation(weakHeadNormalForm(
                    environment_, proofTypeOpened));
            }
        }
        if (!relation) {
            throwElaborate(
                "Quotient.sound(x, y, proof): cannot infer the "
                "equivalence relation `R` — provide an expected type "
                "of the form `Equality(Quotient(T, R), …, …)` or use "
                "the explicit `Quotient.sound(T, R, x, y, proof)` form");
        }
        ExpressionPointer call = makeConstant(
            "Quotient.sound", {universeLevel});
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), relation);
        call = makeApplication(std::move(call), std::move(xKernel));
        call = makeApplication(std::move(call), std::move(yKernel));
        call = makeApplication(std::move(call), std::move(proofKernel));
        return call;
    }

ExpressionPointer Elaborator::desugarAndEliminate(
        SurfaceExpressionPointer handlerSurface,
        SurfaceExpressionPointer conjSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "And.eliminate at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "And.eliminate(handler, conjunction): short form needs "
                "an expected goal type from context; use the 5-arg "
                "verbose form when no expected type is available");
        }
        ExpressionPointer conjKernel = elaborateExpression(
            *conjSurface, localBinders);
        ExpressionPointer conjType = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, conjKernel));
        auto* outerApp = std::get_if<Application>(&conjType->node);
        auto* innerApp = outerApp
            ? std::get_if<Application>(&outerApp->function->node)
            : nullptr;
        auto* head = innerApp
            ? std::get_if<Constant>(&innerApp->function->node)
            : nullptr;
        if (!head || head->name != "And") {
            throwElaborate(
                "And.eliminate(handler, conjunction): second argument's "
                "type must be `And(A, B)`, got `"
                + prettyPrintInLocalScope(conjType, localBinders) + "`");
        }
        ExpressionPointer aProp = innerApp->argument;
        ExpressionPointer bProp = outerApp->argument;
        // Handler's expected type: A → B → Goal. The Pi binders are
        // independent of the codomain, so expectedType (already
        // closed at the call's depth) needs no lifting in the
        // current Pi-codomain position when the surface elaborator
        // matches a Lambda against it.
        ExpressionPointer handlerExpected = makePi("leftProof", aProp,
            makePi("rightProof", bProp, expectedType));
        ExpressionPointer handlerKernel = elaborateExpression(
            *handlerSurface, localBinders, handlerExpected);
        ExpressionPointer aClosed = closeOverLocalBinders(
            aProp, localBinders, localBinders.size());
        ExpressionPointer bClosed = closeOverLocalBinders(
            bProp, localBinders, localBinders.size());
        ExpressionPointer call = makeConstant("And.eliminate", {});
        call = makeApplication(std::move(call), std::move(aClosed));
        call = makeApplication(std::move(call), std::move(bClosed));
        call = makeApplication(std::move(call), expectedType);
        call = makeApplication(std::move(call), std::move(handlerKernel));
        call = makeApplication(std::move(call), std::move(conjKernel));
        return call;
    }

ExpressionPointer Elaborator::desugarOrEliminate(
        SurfaceExpressionPointer handleLeftSurface,
        SurfaceExpressionPointer handleRightSurface,
        SurfaceExpressionPointer disjSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Or.eliminate at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "Or.eliminate(hL, hR, disj): short form needs an "
                "expected goal type from context; use the 6-arg "
                "verbose form when no expected type is available");
        }
        ExpressionPointer disjKernel = elaborateExpression(
            *disjSurface, localBinders);
        ExpressionPointer disjType = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, disjKernel));
        auto* outerApp = std::get_if<Application>(&disjType->node);
        auto* innerApp = outerApp
            ? std::get_if<Application>(&outerApp->function->node)
            : nullptr;
        auto* head = innerApp
            ? std::get_if<Constant>(&innerApp->function->node)
            : nullptr;
        if (!head || head->name != "Or") {
            throwElaborate(
                "Or.eliminate(hL, hR, disj): third argument's type "
                "must be `Or(A, B)`, got `"
                + prettyPrintInLocalScope(disjType, localBinders) + "`");
        }
        ExpressionPointer aProp = innerApp->argument;
        ExpressionPointer bProp = outerApp->argument;
        // Each handler has type A → Goal / B → Goal.
        ExpressionPointer handleLeftExpected = makePi("leftProof",
            aProp, expectedType);
        ExpressionPointer handleRightExpected = makePi("rightProof",
            bProp, expectedType);
        ExpressionPointer handleLeftKernel = elaborateExpression(
            *handleLeftSurface, localBinders, handleLeftExpected);
        ExpressionPointer handleRightKernel = elaborateExpression(
            *handleRightSurface, localBinders, handleRightExpected);
        ExpressionPointer aClosed = closeOverLocalBinders(
            aProp, localBinders, localBinders.size());
        ExpressionPointer bClosed = closeOverLocalBinders(
            bProp, localBinders, localBinders.size());
        ExpressionPointer call = makeConstant("Or.eliminate", {});
        call = makeApplication(std::move(call), std::move(aClosed));
        call = makeApplication(std::move(call), std::move(bClosed));
        call = makeApplication(std::move(call), expectedType);
        call = makeApplication(std::move(call), std::move(handleLeftKernel));
        call = makeApplication(std::move(call), std::move(handleRightKernel));
        call = makeApplication(std::move(call), std::move(disjKernel));
        return call;
    }

ExpressionPointer Elaborator::desugarExistsEliminate(
        SurfaceExpressionPointer handlerSurface,
        SurfaceExpressionPointer witnessSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Exists.eliminate at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "Exists.eliminate(handler, witness): short form needs "
                "an expected goal type from context (e.g. inside a "
                "theorem body); use the 5-arg verbose form "
                "Exists.eliminate(A, P, Goal, handler, witness) "
                "when no expected type is available");
        }
        ExpressionPointer witnessKernel = elaborateExpression(
            *witnessSurface, localBinders);
        ExpressionPointer witnessType = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, witnessKernel));
        // witnessType should be `App(App(Const("Exists"), A), P)`.
        auto* outerApp = std::get_if<Application>(&witnessType->node);
        auto* innerApp = outerApp
            ? std::get_if<Application>(&outerApp->function->node)
            : nullptr;
        auto* head = innerApp
            ? std::get_if<Constant>(&innerApp->function->node)
            : nullptr;
        if (!head || head->name != "Exists") {
            throwElaborate(
                "Exists.eliminate(handler, witness): second argument's "
                "type must be `Exists(A, P)`, got `"
                + prettyPrintInLocalScope(witnessType, localBinders)
                + "`");
        }
        ExpressionPointer aType = innerApp->argument;
        ExpressionPointer predicate = outerApp->argument;
        // Build handler's expected type:
        //   Pi w : A. Pi _ : (predicate w). expectedType
        //
        // `aType` and `predicate` come from inferTypeInLocalContext so
        // they're in OPENED form (Internal FreeVariables for outer
        // local binders). `expectedType` is in CLOSED form — its
        // BoundVariables already index the call-site's locals. As we
        // embed it inside two new Pi binders (w, _), every BV that
        // referenced an outer local must shift by 2 so it still points
        // through past the new binders.
        ExpressionPointer expectedTypeLifted = liftBoundVariables(
            expectedType, 2, 0);
        ExpressionPointer predicateAppliedToW = makeApplication(
            predicate, makeBoundVariable(0));
        ExpressionPointer innerPi = makePi("_",
            std::move(predicateAppliedToW),
            std::move(expectedTypeLifted));
        ExpressionPointer handlerExpected = makePi("w",
            aType, std::move(innerPi));
        ExpressionPointer handlerKernel = elaborateExpression(
            *handlerSurface, localBinders, handlerExpected);
        // Universe argument: Exists's first universe is the carrier's
        // level. Compute it from A's type.
        LevelPointer carrierLevel;
        try {
            ExpressionPointer aTypeOfType = weakHeadNormalForm(
                environment_,
                inferTypeInLocalContext(localBinders, aType));
            auto* aTypeSort = std::get_if<Sort>(&aTypeOfType->node);
            if (!aTypeSort) {
                throwElaborate(
                    "Exists.eliminate: cannot determine the carrier "
                    "type's universe");
            }
            carrierLevel = predecessorOfSortLevel(aTypeSort->level);
        } catch (const TypeError&) {
            throwElaborate(
                "Exists.eliminate: cannot infer the carrier universe");
        }
        // Asymmetric form discipline:
        //   * `expectedType` is in CLOSED form — the caller computed
        //     it at the call site's scope and its BoundVariables
        //     already index the surrounding theorem binders. Use it
        //     directly. Closing it again would bump every BV by
        //     `localBinders.size()`, producing dangling indices.
        //   * `aType` / `predicate` came out of
        //     `inferTypeInLocalContext` and so are in OPENED form
        //     (Internal FreeVariables for the same binders). Close
        //     them to match.
        //   * `handlerKernel` / `witnessKernel` came back from
        //     `elaborateExpression`, which produces CLOSED form, so
        //     they need no transformation.
        ExpressionPointer aClosed = closeOverLocalBinders(
            aType, localBinders, localBinders.size());
        ExpressionPointer pClosed = closeOverLocalBinders(
            predicate, localBinders, localBinders.size());
        ExpressionPointer call = makeConstant(
            "Exists.eliminate", {carrierLevel});
        call = makeApplication(std::move(call), std::move(aClosed));
        call = makeApplication(std::move(call), std::move(pClosed));
        call = makeApplication(std::move(call), expectedType);
        call = makeApplication(std::move(call), std::move(handlerKernel));
        call = makeApplication(std::move(call), std::move(witnessKernel));
        return call;
    }

ExpressionPointer Elaborator::desugarQuotientLift(
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer hSurface,
        SurfaceExpressionPointer qSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.lift at line " + std::to_string(line));
        // Elaborate `q` first to get T from its `Quotient(T, R)` type;
        // then we can build `T → U` as the expected type for `f`, which
        // lets the lambda body's `Quotient.mk` etc. back-infer when
        // they appear in a position whose carrier matches U.
        ExpressionPointer qKernel = elaborateExpression(
            *qSurface, localBinders);
        ExpressionPointer qTypeForT = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, qKernel));
        QuotientDecomposition decompForT;
        if (!tryDecomposeQuotient(qTypeForT, decompForT)) {
            throwElaborate(
                "Quotient.lift(f, h, q): third argument's type must "
                "be `Quotient(T, R)`");
        }
        ExpressionPointer fExpected = nullptr;
        if (expectedType) {
            // Build `T → U` (with U = expectedType) as f's expected type.
            // `decompForT.carrierType` came out of inferType in OPENED form
            // (local-binder references are free variables); close it so the
            // Pi domain matches the closed `expectedType` representation —
            // otherwise a dependent carrier like `CommutativeRing.carrier(c)`
            // / `Wrap(n)` would leak its free `c`/`n` into the function the
            // `Quotient.mk` short form reads its (T, R) from. The codomain
            // gains the new Pi binder, so lift its bound variables by one.
            fExpected = makePi(
                "_",
                closeOverLocalBinders(
                    decompForT.carrierType, localBinders, localBinders.size()),
                liftBoundVariables(expectedType, 1, 0));
        }
        ExpressionPointer fKernel = elaborateExpression(
            *fSurface, localBinders, fExpected);
        ExpressionPointer fTypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, fKernel));
        auto* fPi = std::get_if<Pi>(&fTypeOpened->node);
        if (!fPi) {
            throwElaborate(
                "Quotient.lift(f, h, q): first argument must be a "
                "function `T → U`");
        }
        ExpressionPointer carrierType = closeOverLocalBinders(
            fPi->domain, localBinders, localBinders.size());
        // The lift target `U` must not depend on the argument. When `f`'s
        // body is a `cases`/recursor, the inferred codomain is the
        // *unreduced* `motive(rep)`, which syntactically references the
        // Pi binder even though the motive is constant — WHNF collapses
        // that spurious application so the closed target type doesn't carry
        // an escaping bound variable. (A genuinely dependent `f` survives
        // WHNF still mentioning the binder and fails the lift's own check
        // below, as it should — `Quotient.lift` only lifts non-dependent
        // functions.)
        ExpressionPointer targetType = closeOverLocalBinders(
            weakHeadNormalForm(environment_, fPi->codomain),
            localBinders, localBinders.size());
        // Compute the carrier and target universe levels.
        LevelPointer uLevel;
        LevelPointer vLevel;
        {
            ExpressionPointer carrierTypeOfType = weakHeadNormalForm(
                environment_,
                inferTypeInLocalContext(localBinders, carrierType));
            auto* sortNode =
                std::get_if<Sort>(&carrierTypeOfType->node);
            if (!sortNode) {
                throwElaborate(
                    "Quotient.lift: cannot determine carrier universe");
            }
            uLevel = predecessorOfSortLevel(sortNode->level);
            ExpressionPointer targetTypeOfType = weakHeadNormalForm(
                environment_,
                inferTypeInLocalContext(localBinders, targetType));
            auto* targetSortNode =
                std::get_if<Sort>(&targetTypeOfType->node);
            if (!targetSortNode) {
                throwElaborate(
                    "Quotient.lift: cannot determine target universe");
            }
            vLevel = predecessorOfSortLevel(targetSortNode->level);
        }
        // R from `q`'s type (already decomposed above).
        ExpressionPointer relation = closeOverLocalBinders(
            decompForT.relation, localBinders, localBinders.size());
        // Compute `h`'s expected respect type — `(x y : T) → R(x, y) →
        // f(x) = f(y)` — as the next Pi domain of the lift partially
        // applied to (T, R, U, f). Passing it in lets the lambda-body
        // coercion fire the equality-of-classes wrap (WS3): a respect
        // proof returning the bare equivalence `R(f(x_rep), f(y_rep))`
        // closes the `mk = mk` obligation without naming Quotient.sound.
        ExpressionPointer hExpected = nullptr;
        {
            ExpressionPointer partialCall = makeConstant(
                "Quotient.lift", {uLevel, vLevel});
            partialCall = makeApplication(std::move(partialCall), carrierType);
            partialCall = makeApplication(std::move(partialCall), relation);
            partialCall = makeApplication(std::move(partialCall), targetType);
            partialCall = makeApplication(std::move(partialCall), fKernel);
            try {
                ExpressionPointer partialType = weakHeadNormalForm(
                    environment_,
                    inferTypeInLocalContext(localBinders, partialCall));
                if (auto* pi = std::get_if<Pi>(&partialType->node)) {
                    hExpected = closeOverLocalBinders(
                        pi->domain, localBinders, localBinders.size());
                }
            } catch (...) {
                hExpected = nullptr;
            }
        }
        // Elaborate `h` after we know all the pieces.
        ExpressionPointer hKernel = elaborateExpression(
            *hSurface, localBinders, hExpected);
        // If `h` is a NAMED proof (or any non-lambda) whose type is the
        // bare-equivalence respect property `(…) → R(f x_rep, f y_rep)`
        // rather than the `(…) → f x = f y` the lift wants, the direct
        // elaboration above can't reach the per-leaf class-equality
        // coercion (it only fires on a lambda body). Eta-expand `h` to the
        // respect arity and re-elaborate: the application body then sits in
        // a lambda body and the coercion wraps Quotient.sound. So
        // `well_defined by <named respects lemma>` works, not just an
        // inline `(a b) (e) ↦ …` proof.
        if (hExpected) {
            bool matches = false;
            try {
                ExpressionPointer hTypeOpened = inferTypeInLocalContext(
                    localBinders, hKernel);
                ExpressionPointer hExpectedOpened = openOverLocalBinders(
                    hExpected, localBinders, localBinders.size());
                Context openedContext =
                    buildContextFromLocalBinders(localBinders);
                matches = isDefinitionallyEqual(
                    environment_, openedContext, hTypeOpened, hExpectedOpened);
            } catch (...) {
                matches = true;  // can't tell — leave the direct term
            }
            if (!matches) {
                int respectArity = 0;
                ExpressionPointer cursor = weakHeadNormalForm(
                    environment_, hExpected);
                while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                    respectArity++;
                    cursor = pi->codomain;
                }
                if (respectArity > 0) {
                    std::vector<SurfaceExpressionPointer> applicationArguments;
                    for (int i = 0; i < respectArity; ++i) {
                        applicationArguments.push_back(makeSurfaceIdentifier(
                            "_wellDefinedArgument" + std::to_string(i),
                            {}, line, 0));
                    }
                    SurfaceExpressionPointer etaTerm = makeSurfaceApplication(
                        hSurface, std::move(applicationArguments), line, 0);
                    // Wrap in NESTED single-name lambdas (not one
                    // multi-name binder): each peels exactly one Pi, so a
                    // dependent later domain — `R(x, y)` depending on the
                    // earlier `x`, `y` — is read correctly after the prior
                    // binder is substituted.
                    for (int i = respectArity - 1; i >= 0; --i) {
                        SurfaceBinder etaBinder;
                        etaBinder.names = {
                            "_wellDefinedArgument" + std::to_string(i)};
                        etaTerm = makeSurfaceLambda(
                            std::move(etaBinder), std::move(etaTerm), line, 0);
                    }
                    hKernel = elaborateExpression(
                        *etaTerm, localBinders, hExpected);
                }
            }
        }
        ExpressionPointer call = makeConstant(
            "Quotient.lift", {uLevel, vLevel});
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), relation);
        call = makeApplication(std::move(call), targetType);
        call = makeApplication(std::move(call), std::move(fKernel));
        call = makeApplication(std::move(call), std::move(hKernel));
        call = makeApplication(std::move(call), std::move(qKernel));
        return call;
    }

bool Elaborator::isUnderscorePlaceholder(SurfaceExpressionPointer surface) const {
        if (!surface) return true;
        auto* id = std::get_if<SurfaceIdentifier>(&surface->node);
        return id && id->qualifiedName == "_";
    }

ExpressionPointer Elaborator::inferQuotientMotive(
        ExpressionPointer expectedType,
        ExpressionPointer qKernel,
        ExpressionPointer qTypeOpenedAsDomain,
        const std::vector<LocalBinder>& localBinders) {
        std::string qHeadName = applicationHeadConstantName(qKernel);
        int occurrences = 0;
        int whnfFuel = 2048;
        motiveWalkerCache_.clear();
        ExpressionPointer motiveBody = abstractStructuralOccurrenceWithWHNF(
            expectedType, qKernel, qHeadName,
            /*currentDepth=*/0, occurrences, whnfFuel);
        if (occurrences == 0) {
            // Goal doesn't structurally mention `q`. Constant motive: lift
            // the goal by 1 so BV(0) is reserved for the motive's binder.
            motiveBody = liftBoundVariables(expectedType, +1, 0);
        }
        ExpressionPointer qTypeClosed = closeOverLocalBinders(
            qTypeOpenedAsDomain, localBinders, localBinders.size());
        return makeLambda("_quotientTarget", qTypeClosed, motiveBody);
    }

ExpressionPointer Elaborator::desugarQuotientInduct(
        SurfaceExpressionPointer motiveSurface,
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer qSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.induct at line " + std::to_string(line));
        bool inferMotive = isUnderscorePlaceholder(motiveSurface);
        ExpressionPointer qKernel = elaborateExpression(
            *qSurface, localBinders);
        ExpressionPointer qTypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, qKernel));
        QuotientDecomposition decomp;
        if (!tryDecomposeQuotient(qTypeOpened, decomp)) {
            throwElaborate(
                "Quotient.induct: q's type must be `Quotient(T, R)`");
        }
        ExpressionPointer carrierType = closeOverLocalBinders(
            decomp.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation = closeOverLocalBinders(
            decomp.relation, localBinders, localBinders.size());
        LevelPointer uLevel = decomp.universeLevel;
        ExpressionPointer motiveKernel;
        if (inferMotive) {
            if (!expectedType) {
                throwElaborate(
                    "Quotient.induct with inferred motive (2-arg form or "
                    "`_` in the motive slot) needs an expected type from "
                    "context");
            }
            motiveKernel = inferQuotientMotive(
                expectedType, qKernel, qTypeOpened, localBinders);
        } else {
            motiveKernel = elaborateExpression(
                *motiveSurface, localBinders);
        }
        ExpressionPointer fKernel = elaborateExpression(
            *fSurface, localBinders);
        ExpressionPointer call = makeConstant(
            "Quotient.induct", {uLevel});
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), relation);
        call = makeApplication(std::move(call), std::move(motiveKernel));
        call = makeApplication(std::move(call), std::move(fKernel));
        call = makeApplication(std::move(call), std::move(qKernel));
        return call;
    }

ExpressionPointer Elaborator::inferQuotientMotiveTwo(
        ExpressionPointer expectedType,
        ExpressionPointer q1Kernel,
        ExpressionPointer q2Kernel,
        ExpressionPointer q1TypeOpenedAsDomain,
        ExpressionPointer q2TypeOpenedAsDomain,
        const std::vector<LocalBinder>& localBinders) {
        // Step 1: abstract q2 → BV(0). LocalBinder BVs lifted by +1.
        std::string q2HeadName = applicationHeadConstantName(q2Kernel);
        int occurrences2 = 0;
        int whnfFuel = 4096;
        motiveWalkerCache_.clear();
        ExpressionPointer afterQ2 = abstractStructuralOccurrenceWithWHNF(
            expectedType, q2Kernel, q2HeadName,
            /*currentDepth=*/0, occurrences2, whnfFuel);
        if (occurrences2 == 0) {
            afterQ2 = liftBoundVariables(expectedType, +1, 0);
        }
        // Step 2: wrap in Lambda for q2'.
        ExpressionPointer q2TypeClosed = closeOverLocalBinders(
            q2TypeOpenedAsDomain, localBinders, localBinders.size());
        ExpressionPointer innerLambda = makeLambda(
            "_quotientTarget2", q2TypeClosed, afterQ2);
        // Step 3: abstract q1 in the wrapped expression. The walker
        // descends into the inner Lambda at depth=1; q1 matches there
        // become BV(1), so after the outer wrap they refer to the outer
        // binder. The inner-Lambda's BV(0) (q2 abstraction) is below
        // depth=1, stays at BV(0). LocalBinder BVs (already at +1 from
        // step 1) are at >= 1 inside, so lifted to +2.
        std::string q1HeadName = applicationHeadConstantName(q1Kernel);
        motiveWalkerCache_.clear();
        int occurrences1 = 0;
        ExpressionPointer afterQ1 = abstractStructuralOccurrenceWithWHNF(
            innerLambda, q1Kernel, q1HeadName,
            /*currentDepth=*/0, occurrences1, whnfFuel);
        if (occurrences1 == 0) {
            // q1 doesn't appear in the goal. Lift the entire inner
            // lambda by 1 above threshold 0 to make room for the outer
            // binder.
            afterQ1 = liftBoundVariables(innerLambda, +1, 0);
        }
        // Step 4: wrap in Lambda for q1'.
        ExpressionPointer q1TypeClosed = closeOverLocalBinders(
            q1TypeOpenedAsDomain, localBinders, localBinders.size());
        return makeLambda("_quotientTarget1", q1TypeClosed, afterQ1);
    }

ExpressionPointer Elaborator::desugarQuotientInductTwo(
        SurfaceExpressionPointer motiveSurface,
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer q1Surface,
        SurfaceExpressionPointer q2Surface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.induct_two at line " + std::to_string(line));
        bool inferMotive = isUnderscorePlaceholder(motiveSurface);
        ExpressionPointer q1Kernel = elaborateExpression(
            *q1Surface, localBinders);
        ExpressionPointer q2Kernel = elaborateExpression(
            *q2Surface, localBinders);
        ExpressionPointer q1TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q1Kernel));
        ExpressionPointer q2TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q2Kernel));
        QuotientDecomposition d1, d2;
        if (!tryDecomposeQuotient(q1TypeOpened, d1)) {
            throwElaborate(
                "Quotient.induct_two: q1's type must be `Quotient(T, R)`");
        }
        if (!tryDecomposeQuotient(q2TypeOpened, d2)) {
            throwElaborate(
                "Quotient.induct_two: q2's type must be `Quotient(T, R)`");
        }
        ExpressionPointer carrierType1 = closeOverLocalBinders(
            d1.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation1 = closeOverLocalBinders(
            d1.relation, localBinders, localBinders.size());
        ExpressionPointer carrierType2 = closeOverLocalBinders(
            d2.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation2 = closeOverLocalBinders(
            d2.relation, localBinders, localBinders.size());
        ExpressionPointer motiveKernel;
        if (inferMotive) {
            if (!expectedType) {
                throwElaborate(
                    "Quotient.induct_two with inferred motive (3-arg form "
                    "or `_` in the motive slot) needs an expected type "
                    "from context");
            }
            motiveKernel = inferQuotientMotiveTwo(
                expectedType, q1Kernel, q2Kernel,
                q1TypeOpened, q2TypeOpened, localBinders);
        } else {
            motiveKernel = elaborateExpression(
                *motiveSurface, localBinders);
        }
        ExpressionPointer fKernel = elaborateExpression(
            *fSurface, localBinders);
        ExpressionPointer call = makeConstant(
            "Quotient.induct_two", {d1.universeLevel, d2.universeLevel});
        call = makeApplication(std::move(call), carrierType1);
        call = makeApplication(std::move(call), relation1);
        call = makeApplication(std::move(call), carrierType2);
        call = makeApplication(std::move(call), relation2);
        call = makeApplication(std::move(call), std::move(motiveKernel));
        call = makeApplication(std::move(call), std::move(fKernel));
        call = makeApplication(std::move(call), std::move(q1Kernel));
        call = makeApplication(std::move(call), std::move(q2Kernel));
        return call;
    }

ExpressionPointer Elaborator::inferQuotientMotiveThree(
        ExpressionPointer expectedType,
        ExpressionPointer q1Kernel,
        ExpressionPointer q2Kernel,
        ExpressionPointer q3Kernel,
        ExpressionPointer q1TypeOpenedAsDomain,
        ExpressionPointer q2TypeOpenedAsDomain,
        ExpressionPointer q3TypeOpenedAsDomain,
        const std::vector<LocalBinder>& localBinders) {
        int whnfFuel = 8192;
        // q3 (innermost).
        std::string q3HeadName = applicationHeadConstantName(q3Kernel);
        int occ3 = 0;
        motiveWalkerCache_.clear();
        ExpressionPointer body = abstractStructuralOccurrenceWithWHNF(
            expectedType, q3Kernel, q3HeadName, 0, occ3, whnfFuel);
        if (occ3 == 0) body = liftBoundVariables(expectedType, +1, 0);
        ExpressionPointer q3TypeClosed = closeOverLocalBinders(
            q3TypeOpenedAsDomain, localBinders, localBinders.size());
        body = makeLambda("_quotientTarget3", q3TypeClosed, body);
        // q2.
        std::string q2HeadName = applicationHeadConstantName(q2Kernel);
        int occ2 = 0;
        motiveWalkerCache_.clear();
        ExpressionPointer afterQ2 = abstractStructuralOccurrenceWithWHNF(
            body, q2Kernel, q2HeadName, 0, occ2, whnfFuel);
        if (occ2 == 0) afterQ2 = liftBoundVariables(body, +1, 0);
        ExpressionPointer q2TypeClosed = closeOverLocalBinders(
            q2TypeOpenedAsDomain, localBinders, localBinders.size());
        body = makeLambda("_quotientTarget2", q2TypeClosed, afterQ2);
        // q1.
        std::string q1HeadName = applicationHeadConstantName(q1Kernel);
        int occ1 = 0;
        motiveWalkerCache_.clear();
        ExpressionPointer afterQ1 = abstractStructuralOccurrenceWithWHNF(
            body, q1Kernel, q1HeadName, 0, occ1, whnfFuel);
        if (occ1 == 0) afterQ1 = liftBoundVariables(body, +1, 0);
        ExpressionPointer q1TypeClosed = closeOverLocalBinders(
            q1TypeOpenedAsDomain, localBinders, localBinders.size());
        return makeLambda("_quotientTarget1", q1TypeClosed, afterQ1);
    }

ExpressionPointer Elaborator::desugarQuotientInductThree(
        SurfaceExpressionPointer motiveSurface,
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer q1Surface,
        SurfaceExpressionPointer q2Surface,
        SurfaceExpressionPointer q3Surface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.induct_three at line " + std::to_string(line));
        bool inferMotive = isUnderscorePlaceholder(motiveSurface);
        ExpressionPointer q1Kernel = elaborateExpression(
            *q1Surface, localBinders);
        ExpressionPointer q2Kernel = elaborateExpression(
            *q2Surface, localBinders);
        ExpressionPointer q3Kernel = elaborateExpression(
            *q3Surface, localBinders);
        ExpressionPointer q1TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q1Kernel));
        ExpressionPointer q2TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q2Kernel));
        ExpressionPointer q3TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q3Kernel));
        QuotientDecomposition d1, d2, d3;
        if (!tryDecomposeQuotient(q1TypeOpened, d1)) {
            throwElaborate(
                "Quotient.induct_three: q1's type must be `Quotient(T, R)`");
        }
        if (!tryDecomposeQuotient(q2TypeOpened, d2)) {
            throwElaborate(
                "Quotient.induct_three: q2's type must be `Quotient(T, R)`");
        }
        if (!tryDecomposeQuotient(q3TypeOpened, d3)) {
            throwElaborate(
                "Quotient.induct_three: q3's type must be `Quotient(T, R)`");
        }
        ExpressionPointer carrierType1 = closeOverLocalBinders(
            d1.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation1 = closeOverLocalBinders(
            d1.relation, localBinders, localBinders.size());
        ExpressionPointer carrierType2 = closeOverLocalBinders(
            d2.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation2 = closeOverLocalBinders(
            d2.relation, localBinders, localBinders.size());
        ExpressionPointer carrierType3 = closeOverLocalBinders(
            d3.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation3 = closeOverLocalBinders(
            d3.relation, localBinders, localBinders.size());
        ExpressionPointer motiveKernel;
        if (inferMotive) {
            if (!expectedType) {
                throwElaborate(
                    "Quotient.induct_three with inferred motive (4-arg "
                    "form or `_` in the motive slot) needs an expected "
                    "type from context");
            }
            motiveKernel = inferQuotientMotiveThree(
                expectedType, q1Kernel, q2Kernel, q3Kernel,
                q1TypeOpened, q2TypeOpened, q3TypeOpened, localBinders);
        } else {
            motiveKernel = elaborateExpression(
                *motiveSurface, localBinders);
        }
        ExpressionPointer fKernel = elaborateExpression(
            *fSurface, localBinders);
        ExpressionPointer call = makeConstant(
            "Quotient.induct_three",
            {d1.universeLevel, d2.universeLevel, d3.universeLevel});
        call = makeApplication(std::move(call), carrierType1);
        call = makeApplication(std::move(call), relation1);
        call = makeApplication(std::move(call), carrierType2);
        call = makeApplication(std::move(call), relation2);
        call = makeApplication(std::move(call), carrierType3);
        call = makeApplication(std::move(call), relation3);
        call = makeApplication(std::move(call), std::move(motiveKernel));
        call = makeApplication(std::move(call), std::move(fKernel));
        call = makeApplication(std::move(call), std::move(q1Kernel));
        call = makeApplication(std::move(call), std::move(q2Kernel));
        call = makeApplication(std::move(call), std::move(q3Kernel));
        return call;
    }

LevelPointer Elaborator::predecessorOfSortLevel(LevelPointer sortLevel) {
        if (auto* successor =
                std::get_if<LevelSuccessor>(&sortLevel->node)) {
            return successor->base;
        }
        if (auto* constant =
                std::get_if<LevelConst>(&sortLevel->node)) {
            if (constant->value >= 1) {
                return makeLevelConst(constant->value - 1);
            }
        }
        throwElaborate(
            "internal: cannot derive universe predecessor from sort level");
        return nullptr;  // unreachable
    }

ExpressionPointer Elaborator::desugarCongruenceOf(
        SurfaceExpressionPointer functionSurface,
        SurfaceExpressionPointer equalityProofSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {

        // Elaborate the equality proof first so we know the domain
        // type (from its Equality structure); that lets us accept an
        // untyped lambda for the function argument (bidirectional
        // elaboration of `fun x => body`).
        ExpressionPointer equalityProofKernel =
            elaborateExpression(*equalityProofSurface, localBinders);
        ExpressionPointer equalityProofType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          equalityProofKernel));

        // Pre-extract the domain type from the proof's Equality type
        // so we can hand it to an untyped lambda's elaboration. We use
        // the closed form (BoundVariables for our local binders) so
        // the lambda we construct slots into the surrounding context
        // correctly.
        EqualityComponents proofComponents = extractEqualityComponents(
            equalityProofType, "congruenceOf", line);
        ExpressionPointer domainTypeForLambda = closeOverLocalBinders(
            proofComponents.carrierType,
            localBinders, localBinders.size());

        // Elaborate the function. If it's an untyped single-binder
        // lambda, fill the domain from domainTypeForLambda; otherwise
        // elaborate normally.
        ExpressionPointer functionKernel;
        auto* functionSurfaceLambda =
            std::get_if<SurfaceLambda>(&functionSurface->node);
        if (functionSurfaceLambda
            && !functionSurfaceLambda->binder.type
            && functionSurfaceLambda->binder.names.size() == 1) {
            std::vector<LocalBinder> extended = localBinders;
            extended.push_back(
                {functionSurfaceLambda->binder.names[0],
                 domainTypeForLambda});
            ExpressionPointer lambdaBody = elaborateExpression(
                *functionSurfaceLambda->body, extended);
            functionKernel =
                makeLambda(functionSurfaceLambda->binder.names[0],
                            domainTypeForLambda,
                            std::move(lambdaBody));
        } else {
            functionKernel =
                elaborateExpression(*functionSurface, localBinders);
        }

        // The function's type should be a Pi (A → B). Extract A (the
        // domain) and B (the codomain).
        ExpressionPointer functionType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders, functionKernel));
        auto* functionPi = std::get_if<Pi>(&functionType->node);
        if (!functionPi) {
            throw ElaborateError(
                "congruenceOf: first argument must be a function "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer domainType = functionPi->domain;
        ExpressionPointer codomainType = functionPi->codomain;
        ExpressionPointer leftEndpoint = proofComponents.leftEndpoint;
        ExpressionPointer rightEndpoint = proofComponents.rightEndpoint;

        // Compute universe levels for the domain and codomain types.
        LevelPointer domainUniverseLevel =
            typeUniverseOf(localBinders, leftEndpoint);
        // For the codomain universe level, we need the universe of
        // codomainType. But codomainType lives in a context with one
        // extra binder (the Pi's binder). We re-infer by elaborating
        // in extended context. For non-dependent codomains, the level
        // result has no BoundVariables so it's safe to return as-is.
        std::vector<LocalBinder> piExtended = localBinders;
        piExtended.push_back({functionPi->displayHint, functionPi->domain});
        LevelPointer codomainUniverseLevel;
        {
            ExpressionPointer typeOfCodomain =
                inferTypeInLocalContext(piExtended, codomainType);
            auto* sortNode = std::get_if<Sort>(&typeOfCodomain->node);
            if (!sortNode) {
                throw ElaborateError(
                    "congruenceOf: cannot determine codomain universe");
            }
            LevelPointer sortLevel = sortNode->level;
            if (auto* successorLevel =
                    std::get_if<LevelSuccessor>(&sortLevel->node)) {
                codomainUniverseLevel = successorLevel->base;
            } else if (auto* constant =
                            std::get_if<LevelConst>(&sortLevel->node)) {
                if (constant->value >= 1) {
                    codomainUniverseLevel =
                        makeLevelConst(constant->value - 1);
                } else {
                    throw ElaborateError(
                        "congruenceOf: cannot derive universe predecessor");
                }
            } else {
                throw ElaborateError(
                    "congruenceOf: cannot derive universe predecessor");
            }
        }

        // The endpoints and the domain/codomain came out of the
        // inferred type, which lives in the opened form with
        // FreeVariables for our local binders. Close them back to
        // BoundVariables so they make sense in the calling context —
        // otherwise a stray FreeVariable referring to e.g. a
        // theorem-level binder leaks into the result term and the
        // kernel rejects it as an unbound internal variable.
        ExpressionPointer closedDomainType = closeOverLocalBinders(
            domainType, localBinders, localBinders.size());
        ExpressionPointer closedCodomainType = closeOverLocalBinders(
            codomainType, localBinders, localBinders.size());
        ExpressionPointer closedLeftEndpoint = closeOverLocalBinders(
            leftEndpoint, localBinders, localBinders.size());
        ExpressionPointer closedRightEndpoint = closeOverLocalBinders(
            rightEndpoint, localBinders, localBinders.size());

        // Build Equality.congruence.{u, v}(A, B, f, x, y, proof).
        ExpressionPointer call = makeConstant(
            "Equality.congruence",
            {domainUniverseLevel, codomainUniverseLevel});
        call = makeApplication(std::move(call),
                                std::move(closedDomainType));
        call = makeApplication(std::move(call),
                                std::move(closedCodomainType));
        call = makeApplication(std::move(call), std::move(functionKernel));
        call = makeApplication(std::move(call),
                                std::move(closedLeftEndpoint));
        call = makeApplication(std::move(call),
                                std::move(closedRightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(equalityProofKernel));
        (void)column;
        return call;
    }

bool Elaborator::containsNamedFreeVariable(
        ExpressionPointer expression,
        const std::set<std::string>& names) {
        if (auto* freeVariable =
                std::get_if<FreeVariable>(&expression->node)) {
            return names.count(freeVariable->name) > 0;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return containsNamedFreeVariable(pi->domain, names)
                || containsNamedFreeVariable(pi->codomain, names);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return containsNamedFreeVariable(lambda->domain, names)
                || containsNamedFreeVariable(lambda->body, names);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return containsNamedFreeVariable(application->function, names)
                || containsNamedFreeVariable(application->argument, names);
        }
        return false;
    }


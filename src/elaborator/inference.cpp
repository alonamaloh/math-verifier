// Out-of-line Elaborator method definitions: identifier elaboration, leading-argument & hole inference, constructor-parameter inference, cited-fact bridging, lambda/Pi/numeric-literal forms
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::elaborateIdentifier(
        const SurfaceIdentifier& identifier,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {

        for (int i = static_cast<int>(localBinders.size()) - 1; i >= 0; --i) {
            if (localBinders[i].name == identifier.qualifiedName) {
                int deBruijnIndex =
                    static_cast<int>(localBinders.size()) - 1 - i;
                if (!identifier.universeArgs.empty()) {
                    throw ElaborateError(
                        "local variable '" + identifier.qualifiedName
                        + "' cannot take universe arguments (line "
                        + std::to_string(line) + ")");
                }
                return makeBoundVariable(deBruijnIndex);
            }
        }
        bool isCurrentDeclaration =
            !currentDeclarationName_.empty()
            && currentDeclarationName_ == identifier.qualifiedName;
        const Declaration* environmentDeclaration =
            environment_.lookup(identifier.qualifiedName);
        if (!isCurrentDeclaration && !environmentDeclaration) {
            throw ElaborateError(
                "unknown identifier '" + identifier.qualifiedName
                + "' at line " + std::to_string(line)
                + ", column " + std::to_string(column));
        }
        std::vector<LevelPointer> universeArguments;
        if (!identifier.universeArgs.empty()) {
            for (const auto& level : identifier.universeArgs) {
                universeArguments.push_back(elaborateLevel(*level));
            }
        } else if (isCurrentDeclaration
                   && !currentUniverseParametersOrdered_.empty()) {
            // Self-reference auto-fill: when the inductive or theorem
            // currently being declared mentions itself, the universe
            // arguments are exactly its own universe parameters.
            // External references must always be explicit — universe
            // inference is left for a future iteration.
            for (const auto& parameterName :
                 currentUniverseParametersOrdered_) {
                universeArguments.push_back(makeLevelParam(parameterName));
            }
        } else if (environmentDeclaration
                   && universeParameterCount(*environmentDeclaration) > 0) {
            throw ElaborateError(
                "constant '" + identifier.qualifiedName + "' requires "
                + std::to_string(
                      universeParameterCount(*environmentDeclaration))
                + " universe argument(s); supply them explicitly with "
                ".{...} at line " + std::to_string(line));
        }
        return makeConstant(identifier.qualifiedName,
                            std::move(universeArguments));
    }

std::vector<LevelPointer> Elaborator::universeArgumentsForConstructorCall(
        const Constructor& constructor,
        const Inductive& inductive,
        ExpressionPointer expectedType) {
        const size_t universeParameterCount =
            constructor.universeParameters.size();
        if (universeParameterCount == 0) return {};
        if (expectedType) {
            ExpressionPointer cursor =
                weakHeadNormalForm(environment_, expectedType);
            while (auto* application =
                       std::get_if<Application>(&cursor->node)) {
                cursor = application->function;
            }
            if (auto* constant =
                    std::get_if<Constant>(&cursor->node)) {
                if (constant->name == constructor.inductiveName
                    && constant->universeArguments.size()
                       == universeParameterCount) {
                    return constant->universeArguments;
                }
            }
        }
        (void)inductive;
        std::vector<LevelPointer> zeros;
        for (size_t i = 0; i < universeParameterCount; ++i) {
            zeros.push_back(makeLevelConst(0));
        }
        return zeros;
    }

Elaborator::CallInferenceResult Elaborator::inferLeadingArguments(
        const std::string& diagnosticName,
        ExpressionPointer instantiatedDeclarationType,
        int numLeadingToInfer,
        const std::vector<SurfaceExpressionPointer>& trailingArgumentsSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        const std::string& metavariablePrefix,
        int line) {

        // Open each leading Pi with an Internal-origin FreeVariable
        // serving as a metavariable.
        std::vector<std::string> leadingFreshNames;
        std::set<std::string> metavariableNames;
        // The i-th leading binder's domain, expressed with the earlier
        // leading metavariables (fresh FreeVariables) substituted in.
        // Used by the canonical-instance resolution pass below.
        std::vector<ExpressionPointer> leadingDomains;
        ExpressionPointer cursor = instantiatedDeclarationType;
        for (int i = 0; i < numLeadingToInfer; ++i) {
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) {
                throw ElaborateError(
                    "internal: declaration '" + diagnosticName
                    + "' has fewer leading Pis than expected (line "
                    + std::to_string(line) + ")");
            }
            std::string fresh =
                metavariablePrefix + std::to_string(i) + "_"
                + diagnosticName;
            leadingFreshNames.push_back(fresh);
            metavariableNames.insert(fresh);
            leadingDomains.push_back(pi->domain);
            cursor = openBinder(pi->codomain, fresh,
                                 FreeVariableOrigin::Internal);
        }

        // Backward inference FIRST, before elaborating trailing args.
        // Open every trailing-arg Pi as well (with Internal FreeVars
        // distinct from the leading metavariables), then unify the
        // result against `expectedType` if it was supplied. This lets
        // the trailing-arg elaborations below see fully-resolved
        // expected domain types, which is essential for nested
        // under-applied calls.
        std::map<std::string, ExpressionPointer> assignment;
        if (expectedType) {
            ExpressionPointer resultProbe = cursor;
            for (size_t j = 0;
                 j < trailingArgumentsSurface.size(); ++j) {
                auto* pi = std::get_if<Pi>(&resultProbe->node);
                if (!pi) break;
                std::string trailingArgumentFresh =
                    "_callTrailingArgument_" + std::to_string(j);
                resultProbe = openBinder(pi->codomain,
                                          trailingArgumentFresh,
                                          FreeVariableOrigin::Internal);
            }
            // Structural match first, without unfolding. Works when
            // both sides share the same head.
            unifyConstructorParameters(resultProbe, expectedType,
                                          metavariableNames, assignment);
            // If anything's still unassigned, WHNF both sides and try
            // again. This handles Definition-headed types (e.g.
            // `Natural.divides(_, _)`) by unfolding them to their
            // underlying structure (`Exists(...)`) — metavariables
            // pushed under Lambda binders are now safe to assign,
            // because the unifier shifts them back to the outer scope.
            bool anyLeftUnassigned = false;
            for (const auto& name : leadingFreshNames) {
                if (!assignment.count(name)) {
                    anyLeftUnassigned = true; break;
                }
            }
            if (anyLeftUnassigned) {
                ExpressionPointer expectedTypeNormalised =
                    weakHeadNormalForm(environment_, expectedType);
                ExpressionPointer resultProbeNormalised =
                    weakHeadNormalForm(environment_, resultProbe);
                unifyConstructorParameters(resultProbeNormalised,
                                              expectedTypeNormalised,
                                              metavariableNames, assignment);
            }
        }

        // Walk trailing-arg Pis. For each, elaborate the corresponding
        // surface argument, infer its kernel type, and unify the
        // (metavariable-substituted) Pi domain against the inferred
        // type to fill in any leading values that backward inference
        // didn't resolve. Then descend through the Pi.
        std::vector<ExpressionPointer> elaboratedTrailingArguments;
        for (size_t j = 0; j < trailingArgumentsSurface.size(); ++j) {
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) {
                throw ElaborateError(
                    "call to '" + diagnosticName
                    + "': too many arguments at line "
                    + std::to_string(line));
            }
            ExpressionPointer expectedDomain =
                substituteFreeVariables(pi->domain, assignment);
            // If the expected domain still mentions an unresolved leading
            // metavariable, do NOT hand it to the trailing-arg
            // elaboration: a nested call to the same (or a related)
            // implicit-leading function would backward-bind its own
            // implicits to OUR metavariables, leaving them unresolved —
            // they then leak into the emitted term as unbound
            // FreeVariables (e.g. `PAdic.add(PAdic.add(x, y), z)`).
            // Elaborate the argument bottom-up to a concrete type instead;
            // the unification below still uses `expectedDomain` to solve
            // the metavariables from that concrete type.
            ExpressionPointer expectedForArgument =
                containsNamedFreeVariable(expectedDomain, metavariableNames)
                    ? nullptr
                    : expectedDomain;
            ExpressionPointer kernelTrailingArgument = elaborateExpression(
                *trailingArgumentsSurface[j], localBinders,
                expectedForArgument);
            // Apply the same coercion the plain function-call path gives its
            // arguments (dispatch.cpp): diff-wrap an equality, bridge via a
            // context equality, inject a disjunct, or — the case that makes
            // `witness w with <proposition>` work — auto-prove a bare
            // proposition written where its proof was expected. We WHNF the
            // domain first: after substituting the earlier arguments it is
            // typically an unreduced redex (`(λx. … x …) witness`), and the
            // coercion's cheap prefilter inspects the head/structure, so it
            // would otherwise miss the equality and bare-proposition shapes.
            // Only attempt it when the domain is fully resolved (no leading
            // metavariable left), and it no-ops unless the elaborated
            // argument fails to fit the domain, so existing calls are
            // unaffected.
            if (expectedForArgument) {
                kernelTrailingArgument = coerceToExpectedTypeViaDiff(
                    localBinders, kernelTrailingArgument,
                    weakHeadNormalForm(environment_, expectedForArgument));
            }
            // Infer the trailing arg's type WITHOUT normalising first, so a
            // Definition head (e.g. `Rational.LessOrEqual` for an `a ≤ b`
            // domain) is preserved and matches the Pi domain's head
            // structurally. WHNF only as a fallback below — this mirrors
            // the backward path above. WHNF-ing up front unfolds `a ≤ b`
            // to its `IsNonneg(…)`/`Exists(…)` body, whose head no longer
            // matches the `≤`-shaped domain, leaving the leading
            // metavariables for `a`/`b` unassigned and the whole inference
            // failing for nested calls with no propagated expected type
            // (e.g. `Rational.LessOrEqual.sum(p1, p2)` as a `rewrite` term).
            ExpressionPointer inferredArgumentType =
                closeOverLocalBinders(
                    inferTypeInLocalContext(
                        localBinders, kernelTrailingArgument),
                    localBinders, localBinders.size());
            // Structural attempt first; WHNF both sides as fallback
            // for Definition-headed mismatches. We pass a binder-type
            // stack so the unifier can apply Miller-pattern HO
            // unification when it descends into Pi/Lambda binders and
            // a metavariable head is applied to a local-binder
            // BoundVariable.
            std::vector<ExpressionPointer> binderStack;
            unifyConstructorParameters(expectedDomain,
                                          inferredArgumentType,
                                          metavariableNames, assignment,
                                          0, &binderStack);
            bool anyLeftUnassigned = false;
            for (const auto& name : leadingFreshNames) {
                if (!assignment.count(name)) {
                    anyLeftUnassigned = true; break;
                }
            }
            if (anyLeftUnassigned) {
                ExpressionPointer expectedDomainNormalised =
                    weakHeadNormalForm(environment_, expectedDomain);
                ExpressionPointer inferredArgumentTypeRenormalised =
                    weakHeadNormalForm(environment_,
                                        inferredArgumentType);
                binderStack.clear();
                unifyConstructorParameters(expectedDomainNormalised,
                                              inferredArgumentTypeRenormalised,
                                              metavariableNames, assignment,
                                              0, &binderStack);
            }
            elaboratedTrailingArguments.push_back(kernelTrailingArgument);
            std::string trailingArgumentFresh =
                "_callTrailingArgument_" + std::to_string(j);
            // Bind the trailing-arg placeholder to its elaborated
            // value so that subsequent expectedDomain substitutions for
            // later trailing args (and the final result-pattern
            // unification) don't leak `_callTrailingArgument_N`
            // placeholders into nested constructor inferences — those
            // placeholders would otherwise block assignments via the
            // `containsValueArgumentFreeVar` guard in
            // unifyConstructorParameters.
            assignment[trailingArgumentFresh] = kernelTrailingArgument;
            cursor = openBinder(pi->codomain, trailingArgumentFresh,
                                 FreeVariableOrigin::Internal);
        }

        // Instance resolution (Stage 3 + local-instance follow-on). For
        // any still-unassigned leading implicit whose domain is a
        // PREDICATE application (a structure class like IsGroup/IsRing —
        // head Definition returning Proposition), resolve it either from
        // the canonical-instance registry (concrete or parameterized
        // carrier) OR from a UNIQUE in-scope hypothesis (abstract carrier);
        // either way the sibling operation/identity/… implicits are filled
        // by unifying the chosen instance's type against the domain. The
        // predicate gate keeps ordinary implicits (`{T : Type(0)}`,
        // `{x : Tagged(m)}`) untouched.
        {
            bool madeProgress = true;
            while (madeProgress) {
                madeProgress = false;
                for (int i = 0; i < numLeadingToInfer; ++i) {
                    const std::string& metaName = leadingFreshNames[i];
                    if (assignment.count(metaName)) continue;
                    ExpressionPointer domain = substituteFreeVariables(
                        leadingDomains[i], assignment);
                    std::string structureName = headConstantName(domain);
                    if (structureName == "<unknown>") continue;
                    if (!structureHeadIsClass(structureName)) continue;
                    // First argument of the structure application is the
                    // carrier; collect the spine and read it off.
                    ExpressionPointer spine = domain;
                    ExpressionPointer carrierArgument;
                    while (auto* application =
                               std::get_if<Application>(&spine->node)) {
                        carrierArgument = application->argument;
                        spine = application->function;
                    }
                    if (!carrierArgument) continue;
                    std::string carrierName =
                        headConstantName(carrierArgument);

                    // --- Registry path. Open the instance's leading
                    // parameter Pis as fresh metavariables and unify the
                    // resulting structure application against the domain.
                    // This solves the parameters from WHEREVER they appear
                    // — in the carrier (`IsGroup(IntegerMod(m), …)`) or in
                    // the relation (`IsEquivalenceRelation(Integer,
                    // CongruentModulo(m))`) — and fills the domain's own
                    // sibling metavariables. The instance is then emitted
                    // applied to the solved parameters.
                    auto entry = (carrierName == "<unknown>")
                        ? environment_.canonicalInstanceRegistry.end()
                        : environment_.canonicalInstanceRegistry.find(
                              std::make_tuple(structureName, carrierName));
                    if (entry != environment_.canonicalInstanceRegistry.end()
                        && entry->second.universeParameters.empty()) {
                        std::set<std::string> parameterMetavariables =
                            metavariableNames;
                        std::vector<std::string> parameterMetaNames;
                        ExpressionPointer openedInstanceType =
                            entry->second.type;
                        bool opened = true;
                        for (int k = 0; k < entry->second.parameterCount;
                             ++k) {
                            auto* pi = std::get_if<Pi>(
                                &openedInstanceType->node);
                            if (!pi) { opened = false; break; }
                            std::string fresh = "_instanceParameter_"
                                + std::to_string(k) + "_"
                                + entry->second.termName;
                            parameterMetavariables.insert(fresh);
                            parameterMetaNames.push_back(fresh);
                            openedInstanceType = openBinder(
                                pi->codomain, fresh,
                                FreeVariableOrigin::Internal);
                        }
                        if (opened) {
                            std::map<std::string, ExpressionPointer>
                                instanceAssignment = assignment;
                            // unifyConstructorParameters solves the
                            // metavariables in its FIRST argument. Run both
                            // directions: domain-first solves the domain's
                            // sibling metavariables (operation/identity/…)
                            // from the instance; instance-first solves the
                            // instance's parameters from the domain.
                            unifyConstructorParameters(
                                domain, openedInstanceType,
                                parameterMetavariables, instanceAssignment);
                            unifyConstructorParameters(
                                openedInstanceType, domain,
                                parameterMetavariables, instanceAssignment);
                            bool allSolved = true;
                            for (const auto& p : parameterMetaNames) {
                                if (!instanceAssignment.count(p)) {
                                    allSolved = false; break;
                                }
                            }
                            if (allSolved) {
                                // Merge the sibling domain-metavariable
                                // solutions (substituting the parameters)
                                // into the real assignment.
                                for (const auto& nm : leadingFreshNames) {
                                    if (assignment.count(nm)) continue;
                                    auto it = instanceAssignment.find(nm);
                                    if (it != instanceAssignment.end()) {
                                        assignment[nm] =
                                            substituteFreeVariables(
                                                it->second,
                                                instanceAssignment);
                                    }
                                }
                                ExpressionPointer instanceTerm =
                                    makeConstant(entry->second.termName);
                                for (const auto& p : parameterMetaNames) {
                                    instanceTerm = makeApplication(
                                        std::move(instanceTerm),
                                        instanceAssignment[p]);
                                }
                                assignment[metaName] =
                                    std::move(instanceTerm);
                                madeProgress = true;
                                continue;
                            }
                        }
                    }

                    // --- Local-hypothesis path: abstract carrier. Find a
                    // UNIQUE in-scope binder whose type is the same
                    // structure on a matching carrier; use it as the
                    // instance and read its operations off to fill the
                    // sibling implicits. Work in opened form (FreeVariables
                    // for the local binders), then close the solved values
                    // back; reject on a non-unique match.
                    ExpressionPointer domainOpened = openOverLocalBinders(
                        domain, localBinders, localBinders.size());
                    Context hypothesisContext =
                        buildContextFromLocalBinders(localBinders);
                    int matchCount = 0;
                    int matchBinder = -1;
                    std::map<std::string, ExpressionPointer> matchTrial;
                    for (int j =
                             static_cast<int>(localBinders.size()) - 1;
                         j >= 0; --j) {
                        ExpressionPointer candidateType =
                            openOverLocalBinders(
                                localBinders[j].type, localBinders,
                                static_cast<size_t>(j));
                        if (headConstantName(candidateType)
                            != structureName) {
                            continue;
                        }
                        std::map<std::string, ExpressionPointer> trial;
                        std::vector<ExpressionPointer> binderStack;
                        unifyConstructorParameters(
                            domainOpened, candidateType, metavariableNames,
                            trial, 0, &binderStack);
                        ExpressionPointer resolved =
                            substituteFreeVariables(domainOpened, trial);
                        if (!isDefinitionallyEqual(
                                environment_, hypothesisContext,
                                resolved, candidateType)) {
                            continue;
                        }
                        ++matchCount;
                        matchBinder = j;
                        matchTrial = trial;
                        if (matchCount > 1) break;
                    }
                    if (matchCount == 1) {
                        for (const auto& solvedValue : matchTrial) {
                            if (!assignment.count(solvedValue.first)) {
                                assignment[solvedValue.first] =
                                    closeOverLocalBinders(
                                        solvedValue.second, localBinders,
                                        localBinders.size());
                            }
                        }
                        assignment[metaName] = makeBoundVariable(
                            static_cast<int>(localBinders.size()) - 1
                            - matchBinder);
                        madeProgress = true;
                    }
                }
            }
        }

        // If any leading value still remains unassigned after forward
        // inference, retry the backward unification (now potentially
        // using newly-derived information).
        bool anyUnassigned = false;
        for (const auto& name : leadingFreshNames) {
            if (!assignment.count(name)) { anyUnassigned = true; break; }
        }
        if (anyUnassigned && expectedType) {
            ExpressionPointer resultPattern =
                substituteFreeVariables(cursor, assignment);
            ExpressionPointer expectedTypeNormalised =
                weakHeadNormalForm(environment_, expectedType);
            unifyConstructorParameters(resultPattern,
                                          expectedTypeNormalised,
                                          metavariableNames, assignment);
        }

        // A leading value derived by backward unification against an
        // expectedType that was OPENED over the local binders (e.g. the
        // generic-application path passes `pi->domain` from
        // inferTypeInLocalContext, which is opened) is a pure local-binder
        // FreeVariable term — it must be CLOSED back to BoundVariable form
        // before it is emitted, or the kernel sees an unbound internal
        // variable (`weak(Rational.LessThan.weaken(h))`). Forward-derived
        // values are already closed and contain no such FreeVariable, so
        // they are left untouched. A value can also be MIXED: when a
        // backward-inferred metavariable (opened: local-binder
        // FreeVariables — e.g. the `predicate` of an `∃` taken from an
        // opened expectedType) is combined with a forward-elaborated
        // trailing argument (closed: BoundVariables — e.g. the `∃`'s
        // witness), the resulting value carries BOTH spellings of local
        // binders. Closing such a value directly would shift its already-
        // closed BoundVariables (closeOverLocalBinders shifts
        // unconditionally) and corrupt them. So we first OPEN it fully
        // (turning the closed local-binder BoundVariables back into
        // FreeVariables) and THEN close — a round-trip that normalises
        // opened, closed, and mixed alike to a single closed form.
        std::set<std::string> localBinderOpeningNames;
        for (size_t b = 0; b < localBinders.size(); ++b) {
            localBinderOpeningNames.insert(openingNameFor(localBinders, b));
        }
        CallInferenceResult result;
        std::vector<std::string> unassigned;
        std::vector<std::pair<std::string, ExpressionPointer>> assigned;
        for (const auto& name : leadingFreshNames) {
            auto iterator = assignment.find(name);
            if (iterator == assignment.end()) {
                unassigned.push_back(name);
            } else {
                ExpressionPointer value = iterator->second;
                if (containsNamedFreeVariable(value,
                                              localBinderOpeningNames)) {
                    value = closeOverLocalBinders(
                        openOverLocalBinders(
                            value, localBinders, localBinders.size()),
                        localBinders, localBinders.size());
                }
                // Invariant: an emitted leading value is CLOSED over the
                // local binders. The open-then-close above normalises any
                // mix; assert we never emit a value that still escapes.
                assertClosedOverLocalBinders(
                    value, localBinders, "inferLeadingArguments leading value");
                assigned.push_back({name, value});
                result.leadingValues.push_back(value);
            }
        }
        if (!unassigned.empty()) {
            std::string message =
                "could not infer all leading arguments of '"
                + diagnosticName + "':";
            for (const auto& name : unassigned) {
                // Names are like `_callLeadingArgument_2_Foo`; the
                // index after the prefix tells the user which
                // declaration parameter the elaborator gave up on.
                message += "\n    position ";
                size_t firstUnderscore = name.find('_', 1);
                size_t secondUnderscore = name.find(
                    '_', firstUnderscore + 1);
                if (firstUnderscore != std::string::npos
                    && secondUnderscore != std::string::npos) {
                    message += name.substr(
                        firstUnderscore + 1,
                        secondUnderscore - firstUnderscore - 1);
                } else {
                    message += "(?)";
                }
                message += " is unassigned";
            }
            if (!assigned.empty()) {
                message += "\n  inferred so far:";
                for (const auto& pair : assigned) {
                    message += "\n    ";
                    size_t firstUnderscore = pair.first.find('_', 1);
                    size_t secondUnderscore = pair.first.find(
                        '_', firstUnderscore + 1);
                    if (firstUnderscore != std::string::npos
                        && secondUnderscore != std::string::npos) {
                        message += "position ";
                        message += pair.first.substr(
                            firstUnderscore + 1,
                            secondUnderscore - firstUnderscore - 1);
                    } else {
                        message += pair.first;
                    }
                    message += " = ";
                    message += prettyPrintInLocalScope(
                        pair.second, localBinders);
                }
            }
            if (expectedType) {
                message += "\n  expected return type: ";
                message += prettyPrintInLocalScope(
                    expectedType, localBinders);
            }
            message += "\n  Provide the missing argument(s) explicitly "
                       "to disambiguate.";
            throwElaborate(message);
        }
        result.trailingValues = std::move(elaboratedTrailingArguments);
        return result;
    }

bool Elaborator::typeIsProposition(const Context& context,
                            const ExpressionPointer& openedType) {
        try {
            ExpressionPointer typeOfType =
                inferType(environment_, context, openedType);
            ExpressionPointer reduced =
                weakHeadNormalForm(environment_, typeOfType);
            auto* sortNode = std::get_if<Sort>(&reduced->node);
            if (!sortNode) return false;
            auto* constant =
                std::get_if<LevelConst>(&sortNode->level->node);
            return constant && constant->value == 0;
        } catch (...) {
            return false;
        }
    }

bool Elaborator::termIsProposition(
        const std::vector<LocalBinder>& localBinders,
        const ExpressionPointer& term) {
        ExpressionPointer termType;
        try {
            termType = inferTypeInLocalContext(localBinders, term);
        } catch (...) {
            return false;
        }
        ExpressionPointer reduced =
            weakHeadNormalForm(environment_, termType);
        auto* sortNode = std::get_if<Sort>(&reduced->node);
        if (!sortNode) return false;
        auto* constant =
            std::get_if<LevelConst>(&sortNode->level->node);
        return constant && constant->value == 0;
    }

ExpressionPointer Elaborator::proveCitedFact(
        const ExpressionPointer& factProposition,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        try {
            return autoProveClaim(factProposition, localBinders, line);
        } catch (const ElaborateError&) {
        } catch (const TypeError&) {
        }
        throwElaborate(
            "`by (<fact>)`: couldn't prove the cited fact `"
            + prettyPrintInLocalScope(factProposition, localBinders)
            + "` — the auto-prover can't reach it on its own. Establish it "
            "with its own `claim …;` (or give `by <proof>`) instead.");
    }

bool Elaborator::bridgedResultProvesGoal(
        const ExpressionPointer& result,
        const ExpressionPointer& goalClosed,
        const std::vector<LocalBinder>& localBinders) {
        try {
            ExpressionPointer resultType =
                inferTypeInLocalContext(localBinders, result);
            ExpressionPointer goalOpened = openOverLocalBinders(
                goalClosed, localBinders, localBinders.size());
            Context context = buildContextFromLocalBinders(localBinders);
            return isDefinitionallyEqual(
                environment_, context, resultType, goalOpened);
        } catch (...) {
            return false;
        }
    }

ExpressionPointer Elaborator::bridgeCitedFact(
        const ExpressionPointer& factProposition,
        const ExpressionPointer& goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer proof =
            proveCitedFact(factProposition, localBinders, line);
        // `proof : factProposition` by construction, so use the cited
        // proposition as its (closed) type directly — re-inferring is both
        // unnecessary and unsafe (the auto-prover's result form differs from
        // an elaborated term and can confuse `inferTypeInLocalContext`).
        // Each bridge candidate is *validated* against the goal: a diff that
        // the bridge cannot handle (e.g. a symmetry flip) can return a
        // malformed term rather than throwing, which would crash downstream.
        ExpressionPointer candidate;
        try {
            candidate = autoFillHintForClaim(
                proof, factProposition, goalClosed, localBinders, line);
        } catch (...) { candidate = nullptr; }
        if (candidate && bridgedResultProvesGoal(
                candidate, goalClosed, localBinders)) {
            return candidate;
        }
        try {
            candidate = coerceToExpectedTypeViaDiff(
                localBinders, proof, goalClosed);
        } catch (...) { candidate = nullptr; }
        if (candidate && bridgedResultProvesGoal(
                candidate, goalClosed, localBinders)) {
            return candidate;
        }
        throwElaborate(
            "`by (<fact>)`: proved `"
            + prettyPrintInLocalScope(factProposition, localBinders)
            + "` but it does not establish the goal — the cited fact must be "
            "(or bridge by ring / rewrite / congruence to) the goal.");
    }

ExpressionPointer Elaborator::recoverClaimHint(
        const ExpressionPointer& hintTerm,
        const SurfaceExpression& byHint,
        const ExpressionPointer& goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        if (hintTerm && termIsProposition(localBinders, hintTerm)) {
            return bridgeCitedFact(
                hintTerm, goalClosed, localBinders, line);
        }
        // If the cited name does not exist at all (a typo), say so plainly.
        // This is far clearer than the generic "citation does not prove this
        // goal" below — and necessary, because the recovery attempt would
        // otherwise re-throw "unknown identifier" only to have it masked by
        // our own catch and replaced with the generic message.
        {
            std::string citedName;
            if (auto* identifier =
                    std::get_if<SurfaceIdentifier>(&byHint.node)) {
                citedName = identifier->qualifiedName;
            } else if (auto* application =
                           std::get_if<SurfaceApplication>(&byHint.node)) {
                if (auto* identifier = std::get_if<SurfaceIdentifier>(
                        &application->function->node)) {
                    citedName = identifier->qualifiedName;
                }
            }
            // Only flag QUALIFIED names (containing `.`): those are
            // unambiguously global lemma references, so a missing one is a
            // typo. Bare names can be local hypotheses (a destructured
            // bundle field cited in `by`), overload aliases, or
            // `recalling`-introduced facts — none of which live in the
            // declaration table, so we leave those to the generic path to
            // avoid false "unknown lemma" reports on valid proofs.
            bool isLocalBinder = false;
            for (const auto& binder : localBinders) {
                if (binder.name == citedName) { isLocalBinder = true; break; }
            }
            if (!citedName.empty()
                && citedName.find('.') != std::string::npos
                && !isLocalBinder
                && !environment_.lookup(citedName)) {
                throwElaborate(
                    "unknown lemma `" + citedName + "` in `by` citation — "
                    "no declaration by that name is in scope (check the "
                    "spelling)");
            }
        }
        // Last-ditch recovery: re-elaborate the hint AT the goal type and
        // diff-bridge it (handles `claim f(a) = f(b) by eq` with `eq : a = b`).
        // If that genuinely produces a term of the goal type, return it.
        // Otherwise the citation simply does not apply — and we must say so
        // HERE, naming the hint, its type and the goal. Left to fall through,
        // `coerceToExpectedTypeViaDiff` returns the un-bridged (often bare,
        // unapplied) hint term, and the enclosing theorem typecheck then
        // rejects it with an opaque "proof does not have its declared type"
        // that mentions a bare `(a) → (b) → …` function type — the single
        // most confusing failure when a `by`/`done`/`goal` citation can't
        // infer its arguments or cites the wrong lemma.
        try {
            ExpressionPointer coerced = coerceToExpectedTypeViaDiff(
                localBinders,
                elaborateExpression(byHint, localBinders, goalClosed),
                goalClosed);
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            ExpressionPointer coercedTypeOpened =
                inferTypeInLocalContext(localBinders, coerced);
            ExpressionPointer goalOpened = openOverLocalBinders(
                goalClosed, localBinders, localBinders.size());
            if (isDefinitionallyEqual(environment_, openedContext,
                          coercedTypeOpened, goalOpened)) {
                return coerced;
            }
        } catch (const ElaborateError&) {
            // fall through to the descriptive citation-failure error
        } catch (const TypeError&) {
            // fall through to the descriptive citation-failure error
        }

        // Build a citation-failure message at the claim site.
        std::string hintName;
        if (auto* identifier =
                std::get_if<SurfaceIdentifier>(&byHint.node)) {
            hintName = identifier->qualifiedName;
        } else if (auto* application =
                       std::get_if<SurfaceApplication>(&byHint.node)) {
            if (auto* identifier = std::get_if<SurfaceIdentifier>(
                    &application->function->node)) {
                hintName = identifier->qualifiedName;
            }
        }
        std::string nameQuoted =
            hintName.empty() ? "the `by` hint" : ("`" + hintName + "`");
        std::string message =
            "the " + nameQuoted
            + " citation does not prove this goal\n    goal:        "
            + prettyPrintInLocalScope(goalClosed, localBinders);
        if (hintTerm) {
            ExpressionPointer hintTypeClosed = closeOverLocalBinders(
                inferTypeInLocalContext(localBinders, hintTerm),
                localBinders, localBinders.size());
            message += "\n    " + nameQuoted + " has type: "
                + prettyPrintInLocalScope(hintTypeClosed, localBinders);
        }
        message +=
            "\n  the hint's arguments could not be inferred from the goal "
            "or discharged from context, or its conclusion does not unify "
            "with the goal — check the lemma name, and that the goal (or an "
            "in-scope hypothesis) determines each of its arguments";
        throwElaborate(message);
    }

std::vector<ExpressionPointer> Elaborator::inferCallWithHoles(
        const std::string& diagnosticName,
        ExpressionPointer instantiatedFunctionType,
        const std::vector<SurfaceExpressionPointer>& surfaceArgs,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line,
        const std::set<std::string>* inheritedMetavars,
        std::map<std::string, ExpressionPointer>* solvedInheritedOut) {

        lastDischarges_.clear();
        // Step 1: walk the function's Pi chain. At each position, allocate
        // a fresh Internal FreeVariable. Hole positions add their name to
        // `metavariableNames` (to be resolved by unification); non-hole
        // positions get a name that's later bound to the elaborated value.
        std::vector<std::string> argFreshNames;
        std::vector<bool> isHole;
        std::set<std::string> metavariableNames;
        std::vector<ExpressionPointer> piDomains;
        std::vector<ExpressionPointer> piCodomainsBeforeOpen;
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, instantiatedFunctionType);
        for (size_t i = 0; i < surfaceArgs.size(); ++i) {
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) {
                throw ElaborateError(
                    "call to '" + diagnosticName
                    + "': too many arguments at line "
                    + std::to_string(line));
            }
            bool argIsHole = std::holds_alternative<SurfaceHole>(
                surfaceArgs[i]->node);
            std::string fresh = (argIsHole ? "_hole_" : "_arg_")
                                + std::to_string(i) + "_" + diagnosticName;
            argFreshNames.push_back(fresh);
            isHole.push_back(argIsHole);
            piDomains.push_back(pi->domain);
            piCodomainsBeforeOpen.push_back(pi->codomain);
            if (argIsHole) metavariableNames.insert(fresh);
            cursor = weakHeadNormalForm(environment_,
                openBinder(pi->codomain, fresh,
                            FreeVariableOrigin::Internal));
        }
        // cursor is the result type with all positions opened as FVs.
        ExpressionPointer resultTypePattern = cursor;

        // Backward chaining (Step 5e): the caller's still-unresolved holes are
        // ADDITIONAL solvable metavariables, but ONLY during premise discharge
        // (5c/5e) — never during conclusion/forward unification (Steps 2-4),
        // where they belong to the goal and must stay rigid (otherwise a
        // conclusion like `a := f(?inherited)` would self-unify `?inherited`
        // against itself and lock it). So Steps 2-4 use `metavariableNames`
        // (this call's own holes); the discharge steps use `dischargeMetavars`.
        std::set<std::string> dischargeMetavars = metavariableNames;
        if (inheritedMetavars) {
            dischargeMetavars.insert(inheritedMetavars->begin(),
                                     inheritedMetavars->end());
        }

        // Step 2: backward inference. Unify the result type pattern
        // against the expected type to fix as many hole metavariables
        // as possible up front.
        std::map<std::string, ExpressionPointer> assignment;
        if (expectedType) {
            unifyConstructorParameters(resultTypePattern, expectedType,
                                          metavariableNames, assignment);
            // If anything's still unassigned, try with both sides WHNF'd.
            bool anyUnassigned = false;
            for (const auto& name : metavariableNames) {
                if (!assignment.count(name)) {
                    anyUnassigned = true; break;
                }
            }
            if (anyUnassigned) {
                ExpressionPointer resultPatternNormalised =
                    weakHeadNormalForm(environment_, resultTypePattern);
                ExpressionPointer expectedTypeNormalised =
                    weakHeadNormalForm(environment_, expectedType);
                unifyConstructorParameters(resultPatternNormalised,
                                              expectedTypeNormalised,
                                              metavariableNames, assignment);
            }
            // Class-equality relaxation (WS3): when the goal is
            // `mk(x) = mk(y)` but this function concludes in the underlying
            // relation `R`, unify the result pattern against `R(x, y)` so
            // the holes fill. The result then has type `R(x, y)`, and the
            // equality-of-classes coercion wraps it in Quotient.sound.
            anyUnassigned = false;
            for (const auto& name : metavariableNames) {
                if (!assignment.count(name)) { anyUnassigned = true; break; }
            }
            if (anyUnassigned) {
                if (ExpressionPointer relaxed =
                        relaxClassEqualityToEquivalence(expectedType)) {
                    unifyConstructorParameters(
                        weakHeadNormalForm(environment_, resultTypePattern),
                        weakHeadNormalForm(environment_, relaxed),
                        metavariableNames, assignment);
                }
            }
        }

        // Step 3: forward inference. For each non-hole arg, elaborate it
        // against the Pi domain (with prior metas substituted), unify the
        // inferred type against the domain to fix more hole metas. Bind
        // each non-hole arg's placeholder to its elaborated value so
        // subsequent domains substitute correctly.
        std::vector<ExpressionPointer> elaboratedArgs(surfaceArgs.size(),
                                                       nullptr);
        for (size_t i = 0; i < surfaceArgs.size(); ++i) {
            ExpressionPointer expectedDomain =
                substituteFreeVariables(piDomains[i], assignment);
            if (isHole[i]) continue;
            ExpressionPointer kernelArg = elaborateExpression(
                *surfaceArgs[i], localBinders, expectedDomain);
            ExpressionPointer inferredType =
                weakHeadNormalForm(environment_,
                    inferTypeInLocalContext(
                        localBinders, kernelArg));
            inferredType = closeOverLocalBinders(
                inferredType, localBinders, localBinders.size());
            std::vector<ExpressionPointer> binderStack;
            unifyConstructorParameters(expectedDomain, inferredType,
                                          metavariableNames, assignment,
                                          0, &binderStack);
            bool anyUnassigned = false;
            for (const auto& name : metavariableNames) {
                if (!assignment.count(name)) {
                    anyUnassigned = true; break;
                }
            }
            if (anyUnassigned) {
                ExpressionPointer expectedDomainNormalised =
                    weakHeadNormalForm(environment_, expectedDomain);
                ExpressionPointer inferredRenormalised =
                    weakHeadNormalForm(environment_, inferredType);
                binderStack.clear();
                unifyConstructorParameters(expectedDomainNormalised,
                                              inferredRenormalised,
                                              metavariableNames, assignment,
                                              0, &binderStack);
            }
            elaboratedArgs[i] = kernelArg;
            // Bind this arg's placeholder so later domain substitutions
            // (and the final result pattern unification) see the actual
            // value rather than the FV placeholder.
            assignment[argFreshNames[i]] = kernelArg;
        }

        // Step 4: final backward unification — any holes still
        // unassigned now potentially have more constraints to work with.
        bool anyUnassigned = false;
        for (const auto& name : metavariableNames) {
            if (!assignment.count(name)) { anyUnassigned = true; break; }
        }
        if (anyUnassigned && expectedType) {
            ExpressionPointer resultPatternResolved =
                substituteFreeVariables(resultTypePattern, assignment);
            ExpressionPointer expectedNormalised =
                weakHeadNormalForm(environment_, expectedType);
            unifyConstructorParameters(resultPatternResolved,
                                          expectedNormalised,
                                          metavariableNames, assignment);
        }

        // Step 5: resolve holes from the assignment. Build the final
        // arg list by substituting metavariables.
        std::vector<size_t> unresolved;
        for (size_t i = 0; i < surfaceArgs.size(); ++i) {
            if (isHole[i]) {
                auto iterator = assignment.find(argFreshNames[i]);
                if (iterator == assignment.end()) {
                    unresolved.push_back(i);
                } else {
                    elaboratedArgs[i] = iterator->second;
                }
            }
        }
        // Step 5b: discharge leftover PROOF holes from in-scope hypotheses.
        // A hole the goal didn't pin is typically a side-condition proof
        // argument of a named lemma cited as `by L` (desugared to
        // `L(?, …, ?)`): the conclusion fixes the value holes, leaving a
        // propositional precondition the goal never mentions. If a proof of
        // that exact proposition is already available in the local context,
        // use it — the same precondition discharge the rewrite-lemma index
        // performs (`tryLemmaIndexLookup`). Gated to Prop-typed slots whose
        // type is fully determined (no remaining unresolved hole), so an
        // open VALUE hole — which must come from the goal — is never
        // guessed from context.
        if (!unresolved.empty()) {
            std::set<std::string> stillUnresolvedNames;
            for (size_t idx : unresolved) {
                stillUnresolvedNames.insert(argFreshNames[idx]);
            }
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            std::vector<size_t> remaining;
            for (size_t i : unresolved) {
                ExpressionPointer slotType =
                    substituteFreeVariables(piDomains[i], assignment);
                if (containsNamedFreeVariable(slotType,
                                              stillUnresolvedNames)) {
                    remaining.push_back(i);
                    continue;
                }
                ExpressionPointer slotOpened;
                ExpressionPointer slotNormalised;
                try {
                    slotOpened = openOverLocalBinders(
                        slotType, localBinders, localBinders.size());
                    slotNormalised = weakHeadNormalForm(
                        environment_, slotOpened);
                } catch (const TypeError&) {
                    remaining.push_back(i);
                    continue;
                }
                if (!typeIsProposition(openedContext, slotNormalised)) {
                    remaining.push_back(i);
                    continue;
                }
                bool found = false;
                for (int j = static_cast<int>(localBinders.size()) - 1;
                     j >= 0; --j) {
                    ExpressionPointer candidateType =
                        openOverLocalBinders(
                            localBinders[j].type, localBinders, j);
                    bool eq;
                    try {
                        eq = isDefinitionallyEqual(
                            environment_, openedContext,
                            candidateType, slotNormalised);
                    } catch (const TypeError&) {
                        eq = false;
                    }
                    if (eq) {
                        int deBruijnIndex =
                            static_cast<int>(localBinders.size()) - 1 - j;
                        elaboratedArgs[i] =
                            makeBoundVariable(deBruijnIndex);
                        lastDischarges_.push_back(
                            {deBruijnIndex,
                             static_cast<int>(localBinders.size()),
                             localBinders[j].name});
                        found = true;
                        break;
                    }
                }
                if (!found) remaining.push_back(i);
            }
            unresolved = std::move(remaining);
        }
        // Step 5c: match-and-unify discharge. A slot Step 5b couldn't
        // touch because its type STILL references unresolved holes — e.g.
        // `HasDegree(r, p, d)` where `r`, `p` are value holes the
        // conclusion never pinned (HasDegree_unique's conclusion is just
        // `d = e`). Try UNIFYING the slot pattern against each in-scope
        // hypothesis (local binders — which include `recalling`-bound
        // facts): a match against `HasDegree(Real.ring, modulus, d)`
        // solves `r := Real.ring`, `p := modulus` as a side effect, which
        // then lets the sibling slots discharge. The candidate set is the
        // local context only — bounded, no library search — so the user
        // having cited the lemma + recalled facts licenses the extra
        // unification effort. Iterated to a fixpoint so solved holes
        // propagate to other slots. Only runs on slots that would
        // otherwise error, so it never changes an already-resolved call.
        if (!unresolved.empty()) {
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            int N = static_cast<int>(localBinders.size());
            bool progress = true;
            while (progress && !unresolved.empty()) {
                progress = false;
                std::vector<size_t> stillUnresolved;
                for (size_t i : unresolved) {
                    // A value hole (e.g. the ring/poly of HasDegree_unique)
                    // may have been solved as a side effect of unifying a
                    // sibling proof slot. Resolve it from the assignment
                    // and drop it from the unresolved set.
                    {
                        auto solved = assignment.find(argFreshNames[i]);
                        if (solved != assignment.end()) {
                            elaboratedArgs[i] = solved->second;
                            progress = true;
                            continue;
                        }
                    }
                    ExpressionPointer slotType =
                        substituteFreeVariables(piDomains[i], assignment);
                    ExpressionPointer slotOpened;
                    try {
                        slotOpened = openOverLocalBinders(
                            slotType, localBinders, N);
                    } catch (...) {
                        stillUnresolved.push_back(i); continue;
                    }
                    // No pre-Prop gate here: the slot type still carries
                    // unresolved hole FVs (the very ones we hope to solve),
                    // so it isn't yet well-formed enough to classify. We
                    // check Prop-ness AFTER unification resolves them, which
                    // preserves "never fill a value hole from context".
                    bool filled = false;
                    for (int j = N - 1; j >= 0 && !filled; --j) {
                        ExpressionPointer candidateType =
                            openOverLocalBinders(
                                localBinders[j].type, localBinders, j);
                        // Trial-unify the slot pattern against the
                        // candidate, solving the slot's remaining holes.
                        std::map<std::string, ExpressionPointer> trial =
                            assignment;
                        std::vector<ExpressionPointer> binderStack;
                        try {
                            unifyConstructorParameters(
                                slotOpened, candidateType,
                                dischargeMetavars, trial, 0, &binderStack);
                        } catch (...) { continue; }
                        // Confirm the solved holes make the slot defeq the
                        // candidate (so the hypothesis really proves it).
                        ExpressionPointer slotResolved;
                        try {
                            // Fixpoint substitution: a hole may be solved to a
                            // value that itself mentions another (later-solved)
                            // hole — e.g. backward chaining where `a := f(?inh)`
                            // and `?inh` is solved by this very unification. A
                            // single pass would leave `?inh` and fail the defeq
                            // check; iterate until stable (bounded). Idempotent
                            // when there is no such nesting (the normal path).
                            ExpressionPointer sub = piDomains[i];
                            for (int pass = 0; pass < 4; ++pass) {
                                ExpressionPointer next =
                                    substituteFreeVariables(sub, trial);
                                if (!containsFreeVariable(next)) { sub = next; break; }
                                sub = next;
                            }
                            slotResolved =
                                openOverLocalBinders(sub, localBinders, N);
                        } catch (...) { continue; }
                        bool eq;
                        try {
                            eq = isDefinitionallyEqual(
                                environment_, openedContext,
                                slotResolved, candidateType);
                        } catch (...) { eq = false; }
                        if (!eq) continue;
                        // Only ever discharge a PROOF obligation this way —
                        // never fill a value hole from a same-typed
                        // hypothesis (that must come from the goal).
                        bool resolvedIsProp = false;
                        try {
                            resolvedIsProp = typeIsProposition(
                                openedContext,
                                weakHeadNormalForm(
                                    environment_, slotResolved));
                        } catch (...) { resolvedIsProp = false; }
                        if (!resolvedIsProp) continue;
                        // Commit: adopt the newly-solved holes (closed to
                        // the global closed-over-localBinders form) and
                        // fill this slot with the hypothesis.
                        for (auto& entry : trial) {
                            if (assignment.count(entry.first)) continue;
                            ExpressionPointer closedValue;
                            try {
                                closedValue = closeOverLocalBinders(
                                    entry.second, localBinders, N);
                            } catch (...) { closedValue = entry.second; }
                            assignment[entry.first] = closedValue;
                        }
                        int deBruijnIndex = N - 1 - j;
                        elaboratedArgs[i] =
                            makeBoundVariable(deBruijnIndex);
                        lastDischarges_.push_back(
                            {deBruijnIndex, N, localBinders[j].name});
                        filled = true;
                        progress = true;
                    }
                    if (!filled) stillUnresolved.push_back(i);
                }
                unresolved = std::move(stillUnresolved);
            }
        }
        // Step 5d (backward chaining): a PROOF slot 5b/5c couldn't discharge
        // from a ready-made hypothesis may still be PROVABLE — apply a
        // library lemma and discharge ITS premises from context. Hand the
        // fully-determined Prop slot to the auto-prover, which does exactly
        // that goal-driven search. Bounded to ONE level by
        // backwardChainingDepth_ (the sub-proof's own lemma applications
        // won't re-enter here) and by the auto-prove kernel-step budget
        // (an expensive discharge also trips the by-less warning). Only runs
        // on slots that would otherwise be a hard error, so it never changes
        // an already-resolved call. Toggle off with MATH_BACKWARD_CHAINING=0.
        static const bool backwardChainingEnabled = [] {
            const char* v = std::getenv("MATH_BACKWARD_CHAINING");
            return !(v && std::string(v) == "0");
        }();
        if (!unresolved.empty() && backwardChainingEnabled
            && backwardChainingDepth_ < kBackwardChainDepthCap
            && autoProveDepth_ == 0) {
            std::set<std::string> stillUnresolvedNames;
            for (size_t idx : unresolved) {
                stillUnresolvedNames.insert(argFreshNames[idx]);
            }
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            std::vector<size_t> remaining;
            for (size_t i : unresolved) {
                ExpressionPointer slotType =
                    substituteFreeVariables(piDomains[i], assignment);
                if (containsNamedFreeVariable(slotType,
                                              stillUnresolvedNames)) {
                    remaining.push_back(i);
                    continue;
                }
                ExpressionPointer slotOpened;
                ExpressionPointer slotNormalised;
                try {
                    slotOpened = openOverLocalBinders(
                        slotType, localBinders, localBinders.size());
                    slotNormalised = weakHeadNormalForm(
                        environment_, slotOpened);
                } catch (const TypeError&) {
                    remaining.push_back(i);
                    continue;
                }
                if (!typeIsProposition(openedContext, slotNormalised)) {
                    remaining.push_back(i);
                    continue;
                }
                // slotType is already in closed-over-localBinders form (Step
                // 5b opens it with openOverLocalBinders), which is exactly the
                // `goalClosed` autoProveClaim expects.
                ExpressionPointer proof = nullptr;
                ++backwardChainingDepth_;
                try {
                    proof = autoProveClaim(slotType, localBinders, line);
                } catch (const ElaborateError&) {
                    proof = nullptr;
                } catch (const TypeError&) {
                    proof = nullptr;
                }
                --backwardChainingDepth_;
                if (proof) {
                    elaboratedArgs[i] = proof;
                } else {
                    remaining.push_back(i);
                }
            }
            unresolved = std::move(remaining);
        }
        // Step 5e (general backward chaining): a PROOF slot that STILL mentions
        // an unresolved metavar (so 5b/5c/5d skipped it) may be dischargeable
        // by applying a sub-lemma whose conclusion unifies with the slot AND
        // whose own premise unifies against a context hypothesis — SOLVING the
        // parent metavar as a side effect. tryResolvePremiseSlot shares this
        // call's metavariableNames/assignment so the leaf solution propagates.
        if (!unresolved.empty() && backwardChainingEnabled
            && backwardChainingDepth_ < kBackwardChainDepthCap
            && autoProveDepth_ == 0) {
            // Arm the kernel-step budget if not already (Step 5e is not inside
            // autoProveClaim, which is what normally arms it). Mirrors the
            // arming in autoProveClaim.
            bool armedHere = false;
            if (!autoProveBudgetActive_ && autoProveBudgetLimit_ > 0) {
                autoProveBudgetActive_ = true;
                autoProveBudgetTripped_ = false;
                autoProveStepSnapshot_ = kernelStepsSoFar();
                armedHere = true;
            }
            std::vector<size_t> remaining;
            for (size_t i : unresolved) {
                ExpressionPointer slotType =
                    substituteFreeVariables(piDomains[i], assignment);
                // 5e only handles slots that STILL mention an unresolved
                // metavar (the premise whose hole the conclusion didn't pin).
                // Determined slots are 5d's job (Prop) or are unsolved VALUE
                // holes that a sibling premise's resolution will pin — skip
                // them here so we don't recurse uselessly on data types.
                if (!containsNamedFreeVariable(slotType, dischargeMetavars)) {
                    remaining.push_back(i);
                    continue;
                }
                ExpressionPointer proof = nullptr;
                try {
                    proof = tryResolvePremiseSlot(
                        slotType, localBinders, dischargeMetavars, assignment,
                        backwardChainingDepth_, line);
                } catch (const AutoProverBudgetError&) {
                    proof = nullptr;
                } catch (const ElaborateError&) {
                    proof = nullptr;
                } catch (const TypeError&) {
                    proof = nullptr;
                }
                if (!proof) {
                    // Fallback: the premise mentions one undetermined data
                    // metavar a sub-lemma couldn't pin. Guess it from in-scope
                    // binders and discharge the closed premise with the full
                    // prover (commutativity / ring against context).
                    std::map<std::string, ExpressionPointer> metavarTypes;
                    for (size_t k = 0; k < argFreshNames.size(); ++k) {
                        metavarTypes[argFreshNames[k]] =
                            substituteFreeVariables(piDomains[k], assignment);
                    }
                    try {
                        proof = tryGuessUndeterminedPremise(
                            slotType, metavarTypes, localBinders,
                            dischargeMetavars, assignment, line);
                    } catch (const AutoProverBudgetError&) {
                        proof = nullptr;
                    } catch (const ElaborateError&) {
                        proof = nullptr;
                    } catch (const TypeError&) {
                        proof = nullptr;
                    }
                }
                if (proof) {
                    elaboratedArgs[i] = proof;
                } else {
                    remaining.push_back(i);
                }
            }
            if (armedHere) {
                autoProveBudgetActive_ = false;
                autoProveBudgetTripped_ = false;
            }
            // A sibling slot's value/proof hole may have been solved as a side
            // effect of the unification above; pick those up before erroring.
            std::vector<size_t> stillUnresolved;
            for (size_t i : remaining) {
                auto solved = assignment.find(argFreshNames[i]);
                if (solved != assignment.end()) {
                    elaboratedArgs[i] = solved->second;
                } else {
                    stillUnresolved.push_back(i);
                }
            }
            unresolved = std::move(stillUnresolved);
        }
        // Propagate any of the CALLER's holes this call solved (backward
        // chaining: a leaf unification here may have pinned an inherited
        // metavar) back to the caller via solvedInheritedOut.
        if (inheritedMetavars && solvedInheritedOut) {
            for (const std::string& name : *inheritedMetavars) {
                auto it = assignment.find(name);
                if (it != assignment.end()) {
                    (*solvedInheritedOut)[name] = it->second;
                }
            }
        }
        if (!unresolved.empty()) {
            std::string message =
                "call to '" + diagnosticName
                + "' at line " + std::to_string(line)
                + ": could not infer hole(s) at position";
            if (unresolved.size() > 1) message += "s";
            for (size_t p : unresolved) {
                message += " " + std::to_string(p);
            }
            if (expectedType) {
                message += "\n  expected return type: ";
                message += prettyPrintInLocalScope(
                    expectedType, localBinders);
            }
            message += "\n  Provide the missing argument(s) explicitly "
                       "to disambiguate.";
            throwElaborate(message);
        }
        return elaboratedArgs;
    }

ExpressionPointer Elaborator::elaborateConstructorCallInferringParameters(
        const Constructor& constructor,
        const Inductive& inductive,
        const std::vector<SurfaceExpressionPointer>& valueArgumentsSurface,
        const std::vector<LevelPointer>& universeArguments,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {

        ExpressionPointer constructorType = substituteUniverseLevels(
            constructor.type, constructor.universeParameters,
            universeArguments);
        CallInferenceResult inferred = inferLeadingArguments(
            constructor.inductiveName,
            constructorType,
            inductive.numParameters,
            valueArgumentsSurface,
            localBinders,
            expectedType,
            "_constructorParameter_",
            line);

        const std::string& constructorName =
            inductive.constructorNames[constructor.constructorIndex];
        ExpressionPointer head = makeConstant(constructorName,
                                               universeArguments);
        for (auto& parameterValue : inferred.leadingValues) {
            head = makeApplication(std::move(head),
                                    std::move(parameterValue));
        }
        for (auto& valueArgument : inferred.trailingValues) {
            head = makeApplication(std::move(head),
                                    std::move(valueArgument));
        }
        return head;
    }

ExpressionPointer Elaborator::elaborateNumericLiteral(
        const SurfaceNumericLiteral& numeric,
        int line, int column) {
        // Desugar `25` to successor(successor(...zero)) with 25 successors.
        // Requires Natural, zero, successor to be in the environment.
        if (environment_.lookup("Natural") == nullptr
            || environment_.lookup("zero") == nullptr
            || environment_.lookup("successor") == nullptr) {
            throw ElaborateError(
                "numeric literal at line " + std::to_string(line)
                + " requires Natural, zero, and successor to be in the "
                "environment (import Natural.basics)");
        }
        int value = std::stoi(numeric.digits);
        ExpressionPointer term = makeConstant("zero");
        for (int i = 0; i < value; ++i) {
            term = makeApplication(makeConstant("successor"),
                                    std::move(term));
        }
        (void)column;
        return term;
    }

ExpressionPointer Elaborator::elaboratePiType(
        const SurfacePiType& piType,
        const std::vector<LocalBinder>& localBinders) {
        if (piType.binder.names.empty()) {
            // Anonymous: T → U.
            ExpressionPointer domain =
                elaborateExpression(*piType.binder.type, localBinders);
            std::vector<LocalBinder> extended = localBinders;
            extended.push_back({"_", domain});
            ExpressionPointer codomain =
                elaborateExpression(*piType.codomain, extended);
            return makePi("_", std::move(domain), std::move(codomain));
        }
        // Multi-name binder: (x y z : T) → U becomes a chain of Pis.
        std::vector<LocalBinder> extended = localBinders;
        std::vector<ExpressionPointer> domainsPerName;
        for (const auto& name : piType.binder.names) {
            ExpressionPointer domainHere =
                elaborateExpression(*piType.binder.type, extended);
            domainsPerName.push_back(domainHere);
            extended.push_back({name, domainHere});
        }
        ExpressionPointer codomain =
            elaborateExpression(*piType.codomain, extended);
        ExpressionPointer result = codomain;
        for (int i = static_cast<int>(piType.binder.names.size()) - 1;
             i >= 0; --i) {
            result = makePi(piType.binder.names[i],
                            std::move(domainsPerName[i]),
                            std::move(result));
        }
        return result;
    }

ExpressionPointer Elaborator::elaborateLambda(
        const SurfaceLambda& lambda,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType) {
        if (lambda.binder.names.empty()) {
            throw ElaborateError("lambda binder must have at least one name");
        }
        // Pre-walk the expected Pi if present. Two things drop out:
        //   - per-name domain types (for untyped binders, used directly;
        //     for typed binders, double-checked against the annotation)
        //   - the expected body type after peeling lambda.binder.names
        //     Pi binders, for downstream constructor-parameter inference.
        std::vector<ExpressionPointer> expectedDomainsPerName;
        ExpressionPointer expectedBody = nullptr;
        if (expectedType) {
            // Force opaque heads so a `↦`-lambda body written against an
            // opaque expected type (`IsNonneg(x)`, whose unfolding is the
            // `∀ ε. ε > 0 → …` Pi) can read its binder domains — the
            // structured-construct counterpart of the kernel's retries
            // (replaces `unfold IsNonneg in ((ε)(εpos) ↦ …)`).
            ExpressionPointer cursor =
                weakHeadNormalFormForcingOpaqueHead(expectedType);
            bool ok = true;
            for (size_t k = 0; k < lambda.binder.names.size(); ++k) {
                auto* pi = std::get_if<Pi>(&cursor->node);
                if (!pi) { ok = false; break; }
                expectedDomainsPerName.push_back(pi->domain);
                cursor = weakHeadNormalFormForcingOpaqueHead(pi->codomain);
            }
            if (ok) {
                expectedBody = cursor;
            } else {
                expectedDomainsPerName.clear();
            }
        }
        std::vector<LocalBinder> extended = localBinders;
        std::vector<ExpressionPointer> domainsPerName;
        for (size_t k = 0; k < lambda.binder.names.size(); ++k) {
            const auto& name = lambda.binder.names[k];
            ExpressionPointer domainHere;
            if (lambda.binder.type) {
                domainHere =
                    elaborateExpression(*lambda.binder.type, extended);
            } else {
                // Untyped binder: read the domain from the expected
                // Pi. The kernel term is already in the right scope
                // (it came out of the Pi's domain in the surrounding
                // context); we just need to lift past the binders
                // we've added so far inside this lambda.
                if (k >= expectedDomainsPerName.size()) {
                    throw ElaborateError(
                        "lambda binder '" + name + "' has no type "
                        "annotation and no expected type to infer "
                        "from at this position");
                }
                domainHere = liftBoundVariables(
                    expectedDomainsPerName[k],
                    static_cast<int>(k), 0);
            }
            domainsPerName.push_back(domainHere);
            extended.push_back({name, domainHere});
        }
        ExpressionPointer body =
            elaborateExpression(*lambda.body, extended, expectedBody);
        // Diff-wrap the body if the expected codomain is an equality
        // and the body's type doesn't directly match. Catches
        // `function (rep) => congruenceOf(λ, P)` simplifications
        // where bare `P` would suffice given diff inference.
        if (expectedBody) {
            body = coerceToExpectedTypeViaDiff(
                extended, body, expectedBody);
            checkRedundantCongruenceOfWrapper(
                lambda.body, extended, expectedBody,
                "lambda body");
        }
        // Unused-name warning. Restricted to `suppose ... as`
        // statement-level intros — a `suppose P as h;` whose body
        // ignores `h` is almost always a refactor leftover. Function
        // lambdas (`function (x : T) (y : U) => body`) deliberately
        // do NOT trigger this warning, even when `y` goes unused —
        // C++'s `void foo(int)`-style omission isn't available in
        // this surface yet, and forcing the user to rename to `_y`
        // costs as much as just keeping `y`, so the warning would
        // produce noise without progress. Checked at the SURFACE
        // level (the user's body must textually reference the name)
        // because the elaborator may reference a binder on the
        // user's behalf — e.g. the bare-proposition-as-proof
        // coercion finds hypotheses by type, not by name.
        //
        // Suppress entirely when the body hosts an auto-prover
        // invocation (a by-less calc step, `note`, structured claim,
        // …): such a step can discharge a goal by *type-matching* the
        // supposed hypothesis, consuming it without ever naming it in
        // surface syntax. Without this guard a `suppose H; … calc … =
        // <goal needing H> …` falsely reports H as droppable — and
        // dropping it breaks the proof. Mirrors the same guard on
        // `choose ... such that` (induction.cpp).
        if (lambda.fromStatementIntro
            && lambda.binder.names.size() == 1
            && !surfaceContainsAutoProverInvocation(*lambda.body)) {
            warnIfSurfaceNameUnused(
                lambda.binder.names[0], *lambda.body,
                lambda.body->line, lambda.body->column,
                "`suppose ... as`");
        }
        ExpressionPointer result = body;
        for (int i = static_cast<int>(lambda.binder.names.size()) - 1;
             i >= 0; --i) {
            result = makeLambda(lambda.binder.names[i],
                                std::move(domainsPerName[i]),
                                std::move(result));
        }
        return result;
    }


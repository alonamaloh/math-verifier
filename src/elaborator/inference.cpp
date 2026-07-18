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
                // A transparent alias binder (the quotient descent's
                // scrutinee re-binding, R1) INLINES its value at every
                // use: the elaborated term is byte-identical to writing
                // the value's spelling by hand, so every downstream
                // matcher — auto-prover context scans, lemma index,
                // citation unification — sees the canonical form with no
                // ζ-bridging required. The value is expressed over the
                // binders below the alias; lift it into the use scope.
                if (localBinders[i].inlineAlias && localBinders[i].value) {
                    return liftBoundVariables(
                        localBinders[i].value,
                        static_cast<int>(localBinders.size()) - i, 0);
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
            // §9 error 7: `infinity` is a contextual keyword, legal only
            // as the other side of a trailing-ellipsis series relation.
            if (identifier.qualifiedName == "infinity"
                || identifier.qualifiedName == "∞") {
                throwElaborate(
                    "'" + identifier.qualifiedName + "' is only legal as "
                    "the right-hand side of a series relation "
                    "(t1 + t2 + ... + g + ... = infinity); it is not a "
                    "term");
            }
            std::string message =
                "unknown identifier '" + identifier.qualifiedName
                + "' at line " + std::to_string(line)
                + ", column " + std::to_string(column);
            // Hint for a name that moved out of the universally-imported
            // foundation. `Logic.classical_decidable` is now a theorem in
            // `Natural.classical_decidable` (no longer an axiom in
            // `axioms.math`); the `if P then a else b` conditional
            // desugars to it, so an `if` in a module that doesn't reach
            // that file lands here with the desugared name and an
            // otherwise baffling "unknown identifier" at the `if`.
            if (identifier.qualifiedName == "Logic.classical_decidable") {
                message +=
                    "\n  `Logic.classical_decidable` is a theorem in "
                    "`Natural.classical_decidable` (the `if P then a else "
                    "b` conditional desugars to it) — add `import "
                    "Natural.classical_decidable`";
            }
            // Carry the position structurally too — without it the driver
            // prints the error header at 1:1 and only the message text
            // knows the real location.
            throw ElaborateError(message, line, column);
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
            if (allowImplicitCitationLevels_) {
                // Cited bare (no `.{...}`): fill the universe arguments with
                // fresh placeholder parameters. The citation matcher treats
                // each as a level wildcard when unifying the lemma against the
                // goal, then `completeCitationFromBindings` resolves them to
                // concrete levels from the recovered argument bindings —
                // mirroring how ordinary application elaboration infers `.{u}`
                // from its value arguments.
                size_t count =
                    universeParameterCount(*environmentDeclaration);
                for (size_t i = 0; i < count; ++i) {
                    std::string placeholder =
                        "_cite_u_" + std::to_string(metavarCounter_++);
                    citationLevelPlaceholders_.insert(placeholder);
                    universeArguments.push_back(makeLevelParam(placeholder));
                }
            } else {
                throw ElaborateError(
                    "constant '" + identifier.qualifiedName + "' requires "
                    + std::to_string(
                          universeParameterCount(*environmentDeclaration))
                    + " universe argument(s); supply them explicitly with "
                    ".{...} at line " + std::to_string(line));
            }
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

void Elaborator::resolveStructureClassLeadingImplicits(
        int numLeadingToInfer,
        const std::vector<std::string>& leadingFreshNames,
        const std::vector<ExpressionPointer>& leadingDomains,
        const std::set<std::string>& metavariableNames,
        const std::vector<LocalBinder>& localBinders,
        std::map<std::string, ExpressionPointer>& assignment) {
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
                    continue;
                }

                // --- Forgetful-instance path: derive this structure from a
                // DIFFERENT in-scope structure on the same carrier via a
                // registered forgetful lemma (e.g. `IsGroup` from an in-scope
                // `IsRing` via `IsRing.additive_group`). Only useful once the
                // domain's operations are concrete (the second pass, after
                // backward inference); an abstract domain pins no unique
                // premise, so it is a no-op then.
                ExpressionPointer derived =
                    tryForgetfulDerivation(domain, localBinders,
                                           metavariableNames, assignment);
                if (derived) {
                    assignment[metaName] = std::move(derived);
                    madeProgress = true;
                }
            }
        }
    }

ExpressionPointer Elaborator::tryForgetfulDerivation(
        const ExpressionPointer& targetTypeClosed,
        const std::vector<LocalBinder>& localBinders,
        const std::set<std::string>& outerMetavars,
        std::map<std::string, ExpressionPointer>& outerAssignment) {
        std::string structureName = headConstantName(targetTypeClosed);
        if (structureName == "<unknown>") return nullptr;
        auto bucket =
            environment_.forgetfulInstanceRegistry.find(structureName);
        if (bucket == environment_.forgetfulInstanceRegistry.end()) {
            return nullptr;
        }
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer targetOpened =
            openOverLocalBinders(targetTypeClosed, localBinders, N);
        Context context = buildContextFromLocalBinders(localBinders);

        // Iterated substitution to a fixpoint: a solved hole may map to
        // another (also-solved) hole — e.g. the conclusion binds the lemma's
        // `identity` meta to the caller's `?identity` hole, which the premise
        // then binds to `zero`. A single pass would stop at `?identity`.
        auto resolveFully =
            [this](ExpressionPointer expr,
               const std::map<std::string, ExpressionPointer>& solved) {
            for (int pass = 0; pass < 6; ++pass) {
                ExpressionPointer next = substituteFreeVariables(expr, solved);
                if (compareExpressionStructure(next, expr) == 0) return next;
                expr = next;
            }
            return expr;
        };

        for (const auto& forgetful : bucket->second) {
            // Universe-polymorphic forgetful instances are not yet handled.
            if (!forgetful.universeParameters.empty()) continue;

            // Open the lemma's leading implicit Pis as fresh metavariables;
            // remember the premise domain and the conclusion. The lemma's own
            // metas AND the caller's still-open holes are both solvable here
            // (the latter pinned via the premise hypothesis).
            std::set<std::string> metas = outerMetavars;
            std::vector<std::string> names;
            ExpressionPointer opened = forgetful.type;
            ExpressionPointer premiseDomain;
            bool ok = true;
            for (int k = 0; k < forgetful.leadingImplicitCount; ++k) {
                auto* pi = std::get_if<Pi>(&opened->node);
                if (!pi) { ok = false; break; }
                std::string fresh = "_forgetful_" + std::to_string(k) + "_"
                    + forgetful.termName;
                metas.insert(fresh);
                names.push_back(fresh);
                if (k == forgetful.premiseIndex) premiseDomain = pi->domain;
                opened = openBinder(pi->codomain, fresh,
                                     FreeVariableOrigin::Internal);
            }
            if (!ok || !premiseDomain) continue;
            ExpressionPointer conclusion = opened;

            // Pin the shared carrier/operations from the target conclusion.
            std::map<std::string, ExpressionPointer> trial;
            unifyConstructorParameters(
                conclusion, targetOpened, metas, trial);
            ExpressionPointer premiseResolved =
                resolveFully(premiseDomain, trial);

            // Resolve the premise from a UNIQUE in-scope hypothesis of the
            // premise structure on the matching carrier/operations.
            int matchCount = 0;
            int matchBinder = -1;
            std::map<std::string, ExpressionPointer> matchTrial;
            for (int j = N - 1; j >= 0; --j) {
                ExpressionPointer candidateType = openOverLocalBinders(
                    localBinders[j].type, localBinders,
                    static_cast<size_t>(j));
                if (headConstantName(candidateType)
                    != forgetful.premiseStructureName) {
                    continue;
                }
                std::map<std::string, ExpressionPointer> attempt = trial;
                std::vector<ExpressionPointer> binderStack;
                unifyConstructorParameters(
                    premiseResolved, candidateType, metas, attempt, 0,
                    &binderStack);
                ExpressionPointer resolved =
                    resolveFully(premiseResolved, attempt);
                bool equal;
                try {
                    equal = isDefinitionallyEqual(
                        environment_, context, resolved, candidateType);
                } catch (const TypeError&) {
                    equal = false;
                }
                if (!equal) continue;
                ++matchCount;
                matchBinder = j;
                matchTrial = attempt;
                if (matchCount > 1) break;
            }
            if (matchCount != 1) continue;

            // Every shared operation must have been solved (the premise proof
            // slot is supplied as the matched binder, not a metavariable).
            bool allSolved = true;
            for (int k = 0; k < forgetful.leadingImplicitCount; ++k) {
                if (k == forgetful.premiseIndex) continue;
                ExpressionPointer value =
                    resolveFully(makeFreeVariable(names[k]), matchTrial);
                if (containsNamedFreeVariable(value, metas)) {
                    allSolved = false;
                    break;
                }
            }
            if (!allSolved) continue;

            // Emit the lemma applied to its leading arguments (CLOSED over
            // local binders): shared operations closed from the solved
            // metavariables, the premise proof as the matched binder.
            ExpressionPointer term = makeConstant(forgetful.termName);
            for (int k = 0; k < forgetful.leadingImplicitCount; ++k) {
                ExpressionPointer argument;
                if (k == forgetful.premiseIndex) {
                    argument = makeBoundVariable(N - 1 - matchBinder);
                } else {
                    argument = closeOverLocalBinders(
                        resolveFully(makeFreeVariable(names[k]), matchTrial),
                        localBinders, localBinders.size());
                }
                term = makeApplication(std::move(term), std::move(argument));
            }

            // Write back any caller holes the premise pinned (e.g. the
            // group's `identity`/`inverse`), so sibling slots see them.
            for (const auto& outerName : outerMetavars) {
                if (outerAssignment.count(outerName)) continue;
                ExpressionPointer value =
                    resolveFully(makeFreeVariable(outerName), matchTrial);
                if (containsNamedFreeVariable(value, metas)) continue;
                try {
                    outerAssignment[outerName] = closeOverLocalBinders(
                        value, localBinders, localBinders.size());
                } catch (...) { /* leave unsolved */ }
            }
            return term;
        }
        return nullptr;
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
        // Discharge structure-class implicits (a cited lemma's
        // `ringProof : IsRing(…)`, a typeclass instance) FROM CONTEXT
        // first, BEFORE backward inference matches the conclusion against
        // the goal. The structure proof pins its own operations
        // (`add`/`zero`/…); letting backward inference bind them
        // positionally from the goal instead mis-fires when the citation
        // is used in a congruence/reversed calc step (e.g. the conclusion's
        // constant `zero` aligns with a `multiply(zero, b)` subterm),
        // which then blocks the very discharge that would have pinned them
        // correctly. Only fires for a UNIQUE in-scope structure hypothesis,
        // so it is a no-op when the instance is ambiguous or carrier-driven.
        resolveStructureClassLeadingImplicits(
            numLeadingToInfer, leadingFreshNames, leadingDomains,
            metavariableNames, localBinders, assignment);
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
                // Try the UN-reduced domain first, then the WHNF'd one. The
                // WHNF is needed for the redex / equality / bare-proposition
                // shapes (it exposes the head after substituting earlier
                // arguments), but it also δ-unfolds a relation like `≤`
                // (`Natural.LessOrEqual` is `< ∨ =`) into an `Or`, which
                // defeats the Natural-additive-rearrangement strategy (e) —
                // that prefilters on the relation head. So a `1 + n ≤ d`
                // argument bridges a `successor(n) ≤ d` domain here exactly as
                // it does on the positional path (dispatch.cpp), which passes
                // the un-reduced type. The second attempt no-ops unless the
                // first left the term unchanged, so nothing regresses.
                ExpressionPointer coerced = coerceToExpectedTypeViaDiff(
                    localBinders, kernelTrailingArgument, expectedForArgument);
                if (coerced.get() == kernelTrailingArgument.get()) {
                    coerced = coerceToExpectedTypeViaDiff(
                        localBinders, kernelTrailingArgument,
                        weakHeadNormalForm(environment_, expectedForArgument));
                }
                kernelTrailingArgument = coerced;
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

        // Instance resolution (Stage 3 + local-instance follow-on): see
        // `resolveStructureClassLeadingImplicits`. Run again here — after
        // forward inference — to catch instances whose carrier only the
        // trailing arguments / goal pin (the early pass before backward
        // inference couldn't, with the carrier still a metavariable).
        resolveStructureClassLeadingImplicits(
            numLeadingToInfer, leadingFreshNames, leadingDomains,
            metavariableNames, localBinders, assignment);

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

bool Elaborator::factIsUniversalOverData(
        const Context& openedContext,
        const ExpressionPointer& factTypeOpened) {
        ExpressionPointer cursor;
        try {
            cursor = weakHeadNormalForm(environment_, factTypeOpened);
        } catch (...) {
            return false;
        }
        Context extended = openedContext;
        int dataBinderCount = 0;
        while (auto* pi = std::get_if<Pi>(&cursor->node)) {
            if (typeIsProposition(extended, pi->domain)) break;
            std::string fresh =
                "_forall_fact_" + std::to_string(dataBinderCount);
            extended.push_back({fresh, pi->domain,
                                FreeVariableOrigin::Internal, nullptr});
            try {
                cursor = weakHeadNormalForm(
                    environment_,
                    openBinder(pi->codomain, fresh,
                               FreeVariableOrigin::Internal));
            } catch (...) {
                return false;
            }
            ++dataBinderCount;
        }
        if (dataBinderCount == 0) return false;
        return typeIsProposition(extended, cursor);
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
        // The fact may have become UNNECESSARY rather than wrong: ground
        // arithmetic now computes in the kernel (PLAN_FAST_NUMERALS), so
        // a step once bridged by `(1 + 0 = 1)` can be defeq-trivial with
        // nothing left for the citation to rewrite. Accept when the goal
        // closes on its own — the redundancy checker is the tool that
        // flags the stale hint for deletion.
        try {
            candidate = autoProveClaim(goalClosed, localBinders, line);
        } catch (...) { candidate = nullptr; }
        if (candidate) {
            return candidate;
        }
        throwElaborate(
            "`by (<fact>)`: proved `"
            + prettyPrintInLocalScope(factProposition, localBinders)
            + "` but it does not establish the goal — the cited fact must be "
            "(or bridge by ring / rewrite / congruence to) the goal.");
    }

ExpressionPointer Elaborator::citePiGoalByIntroduction(
        const SurfaceExpression& byHint,
        const ExpressionPointer& goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        // Peel the goal's leading Pis into fresh local binders, in the
        // closed-form convention LocalBinder uses: each Pi's domain is
        // already expressed relative to the binders peeled before it.
        std::vector<LocalBinder> extended = localBinders;
        ExpressionPointer coreGoal = goalClosed;
        while (true) {
            auto* pi = std::get_if<Pi>(&coreGoal->node);
            if (!pi) {
                // A `Not(P)` (or other definition-headed) goal hides
                // its Pi behind one WHNF step — `¬∃ …` goals intro
                // their supposition here.
                ExpressionPointer unfolded =
                    weakHeadNormalForm(environment_, coreGoal);
                if (unfolded.get() == coreGoal.get()) break;
                pi = std::get_if<Pi>(&unfolded->node);
                if (!pi) break;
                coreGoal = unfolded;
            }
            std::string name = pi->displayHint;
            bool collides = name.empty();
            for (const auto& binder : extended) {
                if (binder.name == name) { collides = true; break; }
            }
            if (collides) {
                name = "_cited_intro_"
                    + std::to_string(extended.size() - localBinders.size());
            }
            extended.push_back({name, pi->domain});
            coreGoal = pi->codomain;
        }
        if (extended.size() == localBinders.size()) return nullptr;
        // Run the citation machinery against the core goal with the
        // introduced binders in scope — automating the
        // `(x)(h) ↦ { done by <lemma> }` wrapper idiom. The flattening
        // helper tries the direct citation first, then eliminates
        // Exists-typed introduced binders into their witnesses (the
        // `¬∃ m n. …  by <lemma over m, n>` shape).
        ExpressionPointer result = citeCoreGoalWithExistsFlattening(
            byHint, coreGoal, extended, localBinders.size(),
            /*alreadyEliminated=*/{}, /*depth=*/6, line);
        if (!result) {
            // Mirror the claim flow's recovery against the core goal.
            // No recursion risk: the core goal is Pi-free, so the
            // Pi-introduction branch cannot re-fire.
            try {
                result = recoverClaimHint(
                    nullptr, byHint, coreGoal, extended, line);
            } catch (...) {
                return nullptr;
            }
        }
        if (!result
            || !bridgedResultProvesGoal(result, coreGoal, extended)) {
            return nullptr;
        }
        for (int i = static_cast<int>(extended.size()) - 1;
             i >= static_cast<int>(localBinders.size()); --i) {
            result = makeLambda(extended[i].name,
                                extended[i].type, result);
        }
        return result;
    }

ExpressionPointer Elaborator::citeCoreGoalWithExistsFlattening(
        const SurfaceExpression& byHint,
        ExpressionPointer coreGoal,
        const std::vector<LocalBinder>& binders,
        size_t firstIntroducedIndex,
        std::set<size_t> alreadyEliminated,
        int depth,
        int line) {
        // The direct citation attempt at this scope.
        try {
            ExpressionPointer hintTerm =
                elaborateExpression(byHint, binders, nullptr);
            ExpressionPointer hintType = closeOverLocalBinders(
                inferTypeInLocalContext(binders, hintTerm),
                binders, binders.size());
            ExpressionPointer direct = autoFillHintForClaim(
                hintTerm, hintType, coreGoal, binders, line);
            if (direct
                && bridgedResultProvesGoal(direct, coreGoal, binders)) {
                return direct;
            }
        } catch (const ElaborateError&) {
        } catch (const TypeError&) {
        }
        if (depth <= 0) return nullptr;
        int N = static_cast<int>(binders.size());
        for (int i = N - 1; i >= static_cast<int>(firstIntroducedIndex);
             --i) {
            if (alreadyEliminated.count(i)) continue;
            // Binder types are CLOSED relative to the binders before
            // them; WHNF is safe on that form (bound variables are
            // opaque to reduction).
            ExpressionPointer binderType = weakHeadNormalForm(
                environment_, binders[i].type);
            auto* outerApp = std::get_if<Application>(&binderType->node);
            auto* innerApp = outerApp
                ? std::get_if<Application>(&outerApp->function->node)
                : nullptr;
            auto* head = innerApp
                ? std::get_if<Constant>(&innerApp->function->node)
                : nullptr;
            if (!head) continue;
            // A conjunction-typed binder decomposes into its legs the
            // same way (a nested `∃ … ∧ …` alternates the two): two
            // lambda binders applied to the projections — no motive
            // needed.
            if (head->name == "And") {
                ExpressionPointer leftAtEnd = liftBoundVariables(
                    innerApp->argument, N - i, 0);
                ExpressionPointer rightAtEnd = liftBoundVariables(
                    outerApp->argument, N - i, 0);
                ExpressionPointer rightPastLeft = liftBoundVariables(
                    outerApp->argument, N + 1 - i, 0);
                std::vector<LocalBinder> extended = binders;
                std::string leftName =
                    "_flattened_l_" + std::to_string(i);
                std::string rightName =
                    "_flattened_r_" + std::to_string(i);
                extended.push_back({leftName, leftAtEnd});
                extended.push_back({rightName, rightPastLeft});
                std::set<size_t> eliminated = alreadyEliminated;
                eliminated.insert(i);
                ExpressionPointer inner =
                    citeCoreGoalWithExistsFlattening(
                        byHint, liftBoundVariables(coreGoal, 2, 0),
                        extended, firstIntroducedIndex,
                        std::move(eliminated), depth - 1, line);
                if (!inner) continue;
                ExpressionPointer binderReference =
                    makeBoundVariable(N - 1 - i);
                auto projection = [&](const char* name) {
                    ExpressionPointer p = makeConstant(name, {});
                    p = makeApplication(std::move(p), leftAtEnd);
                    p = makeApplication(std::move(p), rightAtEnd);
                    return makeApplication(std::move(p),
                                            binderReference);
                };
                ExpressionPointer redex = makeLambda(
                    leftName, leftAtEnd,
                    makeLambda(rightName, rightPastLeft, inner));
                redex = makeApplication(std::move(redex),
                                         projection("And.left"));
                redex = makeApplication(std::move(redex),
                                         projection("And.right"));
                return redex;
            }
            if (head->name != "Exists") continue;
            // Lift the components from the binder's position to the
            // current scope's end.
            ExpressionPointer carrierAtEnd = liftBoundVariables(
                innerApp->argument, N - i, 0);
            ExpressionPointer predicateAtEnd = liftBoundVariables(
                outerApp->argument, N - i, 0);
            ExpressionPointer predicatePastWitness = liftBoundVariables(
                outerApp->argument, N + 1 - i, 0);
            std::vector<LocalBinder> extended = binders;
            std::string witnessName =
                "_flattened_w_" + std::to_string(i);
            std::string factName =
                "_flattened_h_" + std::to_string(i);
            extended.push_back({witnessName, carrierAtEnd});
            extended.push_back({factName,
                makeApplication(predicatePastWitness,
                                makeBoundVariable(0))});
            std::set<size_t> eliminated = alreadyEliminated;
            eliminated.insert(i);
            ExpressionPointer inner = citeCoreGoalWithExistsFlattening(
                byHint, liftBoundVariables(coreGoal, 2, 0), extended,
                firstIntroducedIndex, std::move(eliminated), depth - 1,
                line);
            if (!inner) continue;
            // Carrier universe for the eliminator's level argument.
            LevelPointer carrierLevel;
            try {
                ExpressionPointer carrierSort = weakHeadNormalForm(
                    environment_,
                    inferTypeInLocalContext(binders, carrierAtEnd));
                auto* sort = std::get_if<Sort>(&carrierSort->node);
                if (!sort) continue;
                carrierLevel = predecessorOfSortLevel(sort->level);
            } catch (const TypeError&) {
                continue;
            } catch (const ElaborateError&) {
                continue;
            }
            ExpressionPointer handler = makeLambda(
                witnessName, carrierAtEnd,
                makeLambda(factName,
                           makeApplication(predicatePastWitness,
                                           makeBoundVariable(0)),
                           inner));
            ExpressionPointer call = makeConstant(
                "Exists.eliminate", {carrierLevel});
            call = makeApplication(std::move(call), carrierAtEnd);
            call = makeApplication(std::move(call), predicateAtEnd);
            call = makeApplication(std::move(call), coreGoal);
            call = makeApplication(std::move(call), std::move(handler));
            call = makeApplication(std::move(call),
                                    makeBoundVariable(N - 1 - i));
            return call;
        }
        return nullptr;
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
                if (moduleDeclarationNames_.count(citedName)) {
                    throwElaborate(
                        "lemma `" + citedName + "` is declared later in this "
                        "file — declarations must precede their use; move it "
                        "above this citation");
                }
                throwElaborate(
                    "unknown lemma `" + citedName + "` in `by` citation — "
                    "no declaration by that name is in scope (check the "
                    "spelling)");
            }
        }
        // A7 "hypothesis discharge at call sites": `by Lemma(n, k)` with
        // POSITIONAL arguments maps them onto the lemma's DATA
        // parameters (non-Proposition domains) in order; the premise
        // slots become inference holes, discharged from the goal and
        // context like any citation's. A mathematician's "apply the
        // induction hypothesis to n and k". Only reached when the
        // direct application failed, so fully-spelled calls keep their
        // ordinary positional meaning.
        if (auto* application =
                std::get_if<SurfaceApplication>(&byHint.node)) {
            auto* head = std::get_if<SurfaceIdentifier>(
                &application->function->node);
            bool allPositional =
                head != nullptr && !application->arguments.empty();
            if (allPositional) {
                for (const auto& argument : application->arguments) {
                    if (!argument.name.empty()) allPositional = false;
                }
            }
            ExpressionPointer lemmaTypeClosed;
            if (allPositional) {
                int N = static_cast<int>(localBinders.size());
                for (int b = N - 1; b >= 0; --b) {
                    if (localBinders[b].name == head->qualifiedName) {
                        lemmaTypeClosed = liftBoundVariables(
                            localBinders[b].type, N - b, 0);
                        break;
                    }
                }
                if (!lemmaTypeClosed) {
                    if (const Declaration* declaration =
                            environment_.lookup(head->qualifiedName)) {
                        lemmaTypeClosed = declarationType(*declaration);
                    }
                }
            }
            if (lemmaTypeClosed) {
                // Walk the Pi chain in OPENED form, classifying each
                // parameter: data (its domain is a Type) or premise
                // (its domain is a Proposition).
                ExpressionPointer cursor = openOverLocalBinders(
                    lemmaTypeClosed, localBinders, localBinders.size());
                Context chainContext =
                    buildContextFromLocalBinders(localBinders);
                std::vector<bool> premiseSlot;
                while (premiseSlot.size() < 64) {
                    ExpressionPointer normalized =
                        weakHeadNormalForm(environment_, cursor);
                    auto* pi = std::get_if<Pi>(&normalized->node);
                    if (!pi) break;
                    bool isPremise = false;
                    try {
                        ExpressionPointer sort = weakHeadNormalForm(
                            environment_,
                            inferType(environment_, chainContext,
                                      pi->domain));
                        if (auto* asSort = std::get_if<Sort>(&sort->node)) {
                            auto level = levelAsConstant(asSort->level);
                            isPremise = level && *level == 0;
                        }
                    } catch (const TypeError&) {}
                    premiseSlot.push_back(isPremise);
                    std::string opened = "_positional_"
                        + std::to_string(premiseSlot.size());
                    chainContext.push_back(
                        {opened, pi->domain,
                         FreeVariableOrigin::Internal, nullptr});
                    cursor = openBinder(pi->codomain, opened,
                                        FreeVariableOrigin::Internal);
                }
                size_t dataCount = 0;
                for (bool premise : premiseSlot) {
                    if (!premise) ++dataCount;
                }
                if (application->arguments.size() <= dataCount
                    && application->arguments.size()
                           < premiseSlot.size()) {
                    std::vector<SurfaceExpressionPointer> full;
                    size_t argCursor = 0;
                    for (size_t i = 0; i < premiseSlot.size(); ++i) {
                        if (!premiseSlot[i]
                            && argCursor
                                   < application->arguments.size()) {
                            full.push_back(
                                application->arguments[argCursor++]
                                    .value);
                        } else {
                            full.push_back(makeSurfaceHole(line, 0));
                        }
                    }
                    if (argCursor == application->arguments.size()) {
                        SurfaceExpressionPointer rebuilt =
                            makeSurfaceApplication(
                                application->function, std::move(full),
                                line, 0);
                        try {
                            ExpressionPointer filled =
                                elaborateExpression(
                                    *rebuilt, localBinders, goalClosed);
                            if (filled
                                && bridgedResultProvesGoal(
                                       filled, goalClosed,
                                       localBinders)) {
                                return filled;
                            }
                        } catch (const ElaborateError&) {
                        } catch (const TypeError&) {}
                    }
                }
            }
        }
        // All-holes re-citation: a bare `by Lemma` whose structural match
        // failed is retried as the explicit spelling `Lemma(?, …, ?)` the
        // author could write by hand. That form routes through the ordinary
        // call dispatch — the hole solver AND universe inference — which
        // closes citations the first-order conclusion matcher cannot align,
        // e.g. a function-valued conditional (`if P then (a ↦ …) else …`)
        // cited by `Logic.if_positive`, whose branch holes only pin under
        // the goal-directed unifier. Cold path: only reached when the
        // alternative is the citation error, and a failure falls through to
        // that error unchanged.
        if (auto* bareIdentifier =
                std::get_if<SurfaceIdentifier>(&byHint.node)) {
            ExpressionPointer lemmaTypeClosed;
            int N = static_cast<int>(localBinders.size());
            for (int b = N - 1; b >= 0; --b) {
                if (localBinders[b].name == bareIdentifier->qualifiedName) {
                    lemmaTypeClosed = liftBoundVariables(
                        localBinders[b].type, N - b, 0);
                    break;
                }
            }
            if (!lemmaTypeClosed) {
                if (const Declaration* declaration =
                        environment_.lookup(bareIdentifier->qualifiedName)) {
                    lemmaTypeClosed = declarationType(*declaration);
                }
            }
            int leadingPis =
                lemmaTypeClosed ? countLeadingPis(lemmaTypeClosed) : 0;
            if (leadingPis > 0) {
                std::vector<SurfaceExpressionPointer> holes;
                for (int i = 0; i < leadingPis; ++i) {
                    holes.push_back(makeSurfaceHole(line, 0));
                }
                SurfaceExpressionPointer allHolesCall =
                    makeSurfaceApplication(
                        std::make_shared<const SurfaceExpression>(byHint),
                        std::move(holes), line, 0);
                try {
                    ExpressionPointer filled = elaborateExpression(
                        *allHolesCall, localBinders, goalClosed);
                    if (filled
                        && bridgedResultProvesGoal(
                               filled, goalClosed, localBinders)) {
                        return filled;
                    }
                } catch (const ElaborateError&) {
                } catch (const TypeError&) {}
            }
        }
        // Pi-typed goal (structurally, or after one WHNF step — `¬P` is
        // `P → False` behind `Not`): introduce its binders and retry the
        // citation against the inner goal (`claim (x : T) → P by Lemma`
        // cites Lemma at P with x in scope, wrapping the result back
        // into a lambda).
        if (!hintShapeIsProofTerm(byHint)) {
            bool piShaped = std::get_if<Pi>(&goalClosed->node) != nullptr;
            if (!piShaped) {
                ExpressionPointer unfolded =
                    weakHeadNormalForm(environment_, goalClosed);
                piShaped = std::get_if<Pi>(&unfolded->node) != nullptr;
            }
            if (piShaped) {
                ExpressionPointer introduced = citePiGoalByIntroduction(
                    byHint, goalClosed, localBinders, line);
                if (introduced) return introduced;
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
        // Diagnostic captured from the primary `by`-hint elaboration so the
        // failure message can explain WHY the proof didn't apply — its own
        // elaboration error, or the type it actually produced — instead of the
        // bare "an argument could not be inferred". Especially important for
        // tactic hints like `by_induction`, whose internal case-body errors are
        // otherwise swallowed by the fall-through below.
        std::string byHintFailureDetail;
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
            byHintFailureDetail =
                "the `by` proof elaborated but has type:\n        "
                + prettyPrintInLocalScope(
                      closeOverLocalBinders(coercedTypeOpened, localBinders,
                                            localBinders.size()),
                      localBinders);
        } catch (const ElaborateError& error) {
            byHintFailureDetail =
                std::string("the `by` proof did not elaborate:\n    ")
                + error.what();
        } catch (const TypeError& error) {
            byHintFailureDetail =
                std::string("the `by` proof did not typecheck:\n    ")
                + error.what();
        }

        // Symmetry bridge inside Not: the goal is ¬(a = b) and the
        // citation proves ¬(b = a). The bare-claim auto-prover already
        // crosses this gap (it finds the lemma by index and flips the
        // inner equality); an EXPLICIT citation of the very same lemma
        // used to fail here, forcing authors to choose between an
        // unexplained bare claim and a wrong-feeling error. Wrap as
        //   (h : a = b) ↦ cited(Equality.symmetry(h)) : False.
        try {
            int N = static_cast<int>(localBinders.size());
            ExpressionPointer goalOpened = openOverLocalBinders(
                goalClosed, localBinders, N);
            ExpressionPointer goalWhnf = weakHeadNormalForm(
                environment_, goalOpened);
            auto* notPi = std::get_if<Pi>(&goalWhnf->node);
            bool codomainIsFalse = false;
            if (notPi && !referencesBoundVariable(notPi->codomain, 0)) {
                ExpressionPointer codomainWhnf = weakHeadNormalForm(
                    environment_, shift(notPi->codomain, -1));
                auto* codomainConstant =
                    std::get_if<Constant>(&codomainWhnf->node);
                codomainIsFalse = codomainConstant
                    && codomainConstant->name == "False";
            }
            if (codomainIsFalse) {
                EqualityComponents components = extractEqualityComponents(
                    notPi->domain, "symmetry-inside-Not bridge", line);
                // The flipped proposition ¬(b = a), closed over the
                // local binders, as the citation's expected type.
                ExpressionPointer flippedEquality = makeConstant(
                    "Equality", {components.carrierUniverseLevel});
                flippedEquality = makeApplication(
                    flippedEquality, components.carrierType);
                flippedEquality = makeApplication(
                    flippedEquality, components.rightEndpoint);
                flippedEquality = makeApplication(
                    flippedEquality, components.leftEndpoint);
                ExpressionPointer flippedNotOpened = makePi(
                    "flipped", flippedEquality, shift(notPi->codomain, 0));
                ExpressionPointer flippedNotClosed = closeOverLocalBinders(
                    flippedNotOpened, localBinders, N);
                // Cite the hint against the FLIPPED proposition with the
                // same goal-driven engine a direct citation gets
                // (conclusion match-and-unify + premise discharge); raw
                // re-elaboration can't instantiate a Pi-lemma's
                // arguments from the expected type.
                ExpressionPointer citedAtFlipped = nullptr;
                if (hintTerm) {
                    ExpressionPointer hintTypeOpened =
                        inferTypeInLocalContext(localBinders, hintTerm);
                    ExpressionPointer hintTypeClosed = closeOverLocalBinders(
                        hintTypeOpened, localBinders, N);
                    try {
                        citedAtFlipped = autoFillHintForClaim(
                            hintTerm, hintTypeClosed, flippedNotClosed,
                            localBinders, line);
                    } catch (const ElaborateError&) {
                        citedAtFlipped = nullptr;
                    } catch (const TypeError&) {
                        citedAtFlipped = nullptr;
                    }
                }
                if (!citedAtFlipped) {
                    citedAtFlipped = elaborateExpression(
                        byHint, localBinders, flippedNotClosed);
                }
                // (h : a = b) ↦ cited(Equality.symmetry(T, a, b, h))
                ExpressionPointer symmetric = makeConstant(
                    "Equality.symmetry",
                    {components.carrierUniverseLevel});
                for (ExpressionPointer piece :
                     {shift(components.carrierType, 1),
                      shift(components.leftEndpoint, 1),
                      shift(components.rightEndpoint, 1),
                      makeBoundVariable(0)}) {
                    symmetric = makeApplication(symmetric, piece);
                }
                ExpressionPointer citedOpened = openOverLocalBinders(
                    citedAtFlipped, localBinders, N);
                ExpressionPointer bridgedOpened = makeLambda(
                    "flippedEquality", notPi->domain,
                    makeApplication(shift(citedOpened, 1), symmetric));
                ExpressionPointer bridged = closeOverLocalBinders(
                    bridgedOpened, localBinders, N);
                Context openedContext =
                    buildContextFromLocalBinders(localBinders);
                ExpressionPointer bridgedTypeOpened =
                    inferTypeInLocalContext(localBinders, bridged);
                if (isDefinitionallyEqual(environment_, openedContext,
                                          bridgedTypeOpened, goalOpened)) {
                    return bridged;
                }
            }
        } catch (const ElaborateError&) {
            // fall through to the descriptive citation-failure error
        } catch (const TypeError&) {
            // fall through to the descriptive citation-failure error
        }

        // Last attempts before erroring — claims and calc steps are one
        // language, so a hint that closes a calc step must close the same
        // statement as a claim. These mirror the calc `=`-step mismatch
        // pipeline (rewrite → bare-lemma-at-diff → equality diff-wrap);
        // all three are cold paths, running only when the alternative is
        // the citation error.
        //
        // (1) Bare-lemma congruence (tryApplyBareLemmaToDiff): the cited
        // lemma is un-applied and its conclusion matches the goal
        // equality's differing SUBTERM (not the whole equality) — solve
        // its arguments against that subterm, discharge premises, wrap in
        // congruence. Closes `Sum.left(make(v, p)) = Sum.left(element)
        // by equal_of_value` exactly as the calc step spelling does.
        if (hintTerm) {
            try {
                ExpressionPointer goalOpenedEq = weakHeadNormalForm(
                    environment_,
                    openOverLocalBinders(goalClosed, localBinders,
                                         localBinders.size()));
                EqualityComponents goalComps = extractEqualityComponents(
                    goalOpenedEq, "claim bare-lemma diff", line);
                ExpressionPointer previousKernel = closeOverLocalBinders(
                    goalComps.leftEndpoint, localBinders,
                    localBinders.size());
                ExpressionPointer nextKernel = closeOverLocalBinders(
                    goalComps.rightEndpoint, localBinders,
                    localBinders.size());
                ExpressionPointer hintTypeClosedForBare =
                    closeOverLocalBinders(
                        inferTypeInLocalContext(localBinders, hintTerm),
                        localBinders, localBinders.size());
                if (std::holds_alternative<Pi>(
                        hintTypeClosedForBare->node)) {
                    ExpressionPointer bareAttempt = tryApplyBareLemmaToDiff(
                        localBinders, previousKernel, nextKernel,
                        hintTerm, hintTypeClosedForBare, line, 0);
                    if (bareAttempt) {
                        ExpressionPointer bareTypeOpened =
                            inferTypeInLocalContext(localBinders,
                                                    bareAttempt);
                        Context openedContext =
                            buildContextFromLocalBinders(localBinders);
                        ExpressionPointer goalOpenedForCheck =
                            openOverLocalBinders(goalClosed, localBinders,
                                                 localBinders.size());
                        if (isDefinitionallyEqual(environment_,
                                                  openedContext,
                                                  bareTypeOpened,
                                                  goalOpenedForCheck)) {
                            return bareAttempt;
                        }
                    }
                }
            } catch (const ElaborateError&) {
                // fall through
            } catch (const TypeError&) {
                // fall through
            }
        }
        // (2) The calc `=`-step auto-rewrite fallback (calc.cpp): rewrite
        // the goal equality with the cited lemma — instantiating it at the
        // matching subterm under congruence, premises discharged — exactly
        // as a calc step would. This is the mechanism that closes
        // `f(g(x)) = f(y) by lemma : g(x) = y`-shaped citations.
        {
            ExpressionPointer rewriteAttempt;
            try {
                rewriteAttempt = desugarRewrite(
                    std::make_shared<const SurfaceExpression>(byHint),
                    localBinders, goalClosed, line, 0);
            } catch (const ElaborateError&) {
                rewriteAttempt = nullptr;
            } catch (const TypeError&) {
                rewriteAttempt = nullptr;
            }
            if (rewriteAttempt) {
                // Speculative: verify the candidate really proves the goal
                // (same guard as the calc step's rewrite fallback).
                try {
                    ExpressionPointer rewriteTypeOpened =
                        inferTypeInLocalContext(localBinders,
                                                rewriteAttempt);
                    ExpressionPointer goalOpenedForCheck =
                        openOverLocalBinders(goalClosed, localBinders,
                                             localBinders.size());
                    Context openedContext =
                        buildContextFromLocalBinders(localBinders);
                    if (isDefinitionallyEqual(environment_, openedContext,
                                              rewriteTypeOpened,
                                              goalOpenedForCheck)) {
                        return rewriteAttempt;
                    }
                } catch (const TypeError&) {
                } catch (const ElaborateError&) {
                }
            }
        }
        // (3) The calc `=`-step diff-inference: a cited equality lemma
        // whose conclusion proves the goal at a single differing position
        // (under congruence) closes here exactly as it closes a calc step.
        if (hintTerm) {
            ExpressionPointer hintTypeForDiff;
            try {
                hintTypeForDiff = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, hintTerm),
                    localBinders, localBinders.size());
            } catch (const TypeError&) {
                hintTypeForDiff = nullptr;
            } catch (const ElaborateError&) {
                hintTypeForDiff = nullptr;
            }
            if (hintTypeForDiff) {
                ExpressionPointer wrapped = tryDiffWrapForEqualityGoal(
                    localBinders, hintTerm, hintTypeForDiff, goalClosed);
                if (wrapped) return wrapped;
            }
        }

        // (4) The norm_cast normalization bridge: the hint proves the goal
        // once a registered ground equality (`from_real(Real.zero) =
        // RingModulo.zero`) is applied. Lets `conjugate_zero : conj(0) = 0`
        // close a `conj(RingModulo.zero) = …` consumer without the verbose
        // carrier-constant restatement. Validated defeq against the goal
        // inside the helper.
        if (hintTerm) {
            ExpressionPointer bridged = tryNormalizationEqualityBridge(
                localBinders, hintTerm, goalClosed, line);
            if (bridged) return bridged;
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
            hintName.empty() ? "`by` hint" : ("`" + hintName + "`");
        std::string message =
            "the " + nameQuoted
            + " citation does not prove this goal\n    goal:        "
            + prettyPrintInLocalScope(goalClosed, localBinders);
        // Split the failure into its two distinguishable causes instead of
        // listing both every time. Compare the lemma's CONCLUSION head (peel
        // its Pis) against the goal's head. The DECISION uses WHNF'd heads so a
        // definitional alias (`≤` vs its `Or`/`IsNonneg` unfolding) doesn't read
        // as a mismatch; the DISPLAY uses the raw heads so the user sees the
        // name they wrote (`Natural.LessOrEqual`, not `Or`). Different heads ⇒
        // the lemma doesn't target this goal; same head ⇒ the conclusion shape
        // fits but an argument/premise couldn't be pinned.
        std::string conclusionHeadRaw;
        std::string conclusionHeadWhnf;
        ExpressionPointer conclusionWhnfForHeads;
        if (hintTerm) {
            ExpressionPointer hintTypeClosed = closeOverLocalBinders(
                inferTypeInLocalContext(localBinders, hintTerm),
                localBinders, localBinders.size());
            message += "\n    " + nameQuoted + " has type: "
                + prettyPrintInLocalScope(hintTypeClosed, localBinders);
            // Peel Pis to reach the raw conclusion: WHNF only to *detect* a Pi
            // head, but descend into the un-normalised codomain so the
            // conclusion keeps its surface spelling.
            ExpressionPointer conclusion = hintTypeClosed;
            while (auto* pi = std::get_if<Pi>(
                       &weakHeadNormalForm(environment_, conclusion)->node)) {
                conclusion = pi->codomain;
            }
            conclusionHeadRaw = headConstantName(conclusion);
            conclusionWhnfForHeads =
                weakHeadNormalForm(environment_, conclusion);
            conclusionHeadWhnf = headConstantName(conclusionWhnfForHeads);
        }
        std::string goalHeadRaw = headConstantName(goalClosed);
        std::string goalHeadWhnf = headConstantName(
            weakHeadNormalForm(environment_, goalClosed));
        // A citation whose conclusion genuinely targets this goal shape
        // may still fail to INSTANTIATE — e.g. a slot pinned by two
        // spellings the matcher cannot reconcile (`monus(0 + b, 0) = b`
        // by `monus_zero`: the slot wants both `0 + b` and `b`). When
        // the by-less prover closes the same goal — typically through
        // the very lemma cited, via its index — accept: claims and calc
        // steps are one language, and a signpost hint must not fail a
        // goal the bare claim proves. A lemma about a DIFFERENT head
        // still errors loudly below (a wrong name stays a wrong name);
        // for EQUALITY conclusions the relation head alone is vacuous
        // (every equality lemma "matches" every equality goal), so an
        // endpoint head must agree too — `multiply_commutative` cited
        // on an `add` goal stays an error even when the goal happens to
        // auto-close.
        bool conclusionTargetsGoal =
            !conclusionHeadWhnf.empty() && !goalHeadWhnf.empty()
            && conclusionHeadWhnf == goalHeadWhnf;
        if (conclusionTargetsGoal && conclusionHeadWhnf == "Equality"
            && hintTerm) {
            auto endpointHead =
                [&](ExpressionPointer equality, bool left)
                    -> std::string {
                auto* outer = std::get_if<Application>(&equality->node);
                if (!outer) return std::string();
                if (!left) return headConstantName(outer->argument);
                auto* inner =
                    std::get_if<Application>(&outer->function->node);
                return inner ? headConstantName(inner->argument)
                             : std::string();
            };
            ExpressionPointer conclusionForHeads = conclusionWhnfForHeads;
            if (conclusionForHeads) {
                std::string goalLeft = endpointHead(
                    weakHeadNormalForm(environment_, goalClosed), true);
                std::string goalRight = endpointHead(
                    weakHeadNormalForm(environment_, goalClosed), false);
                std::string conclusionLeft =
                    endpointHead(conclusionForHeads, true);
                std::string conclusionRight =
                    endpointHead(conclusionForHeads, false);
                bool someEndpointAgrees =
                    (!conclusionLeft.empty()
                     && (conclusionLeft == goalLeft
                         || conclusionLeft == goalRight))
                    || (!conclusionRight.empty()
                        && (conclusionRight == goalLeft
                            || conclusionRight == goalRight));
                bool conclusionEndpointsBare =
                    conclusionLeft.empty() && conclusionRight.empty();
                conclusionTargetsGoal =
                    someEndpointAgrees || conclusionEndpointsBare;
            }
        }
        if (conclusionTargetsGoal) {
            ExpressionPointer unaided;
            try {
                unaided = autoProveClaim(goalClosed, localBinders, line);
            } catch (...) { unaided = nullptr; }
            if (unaided) {
                return unaided;
            }
        }
        if (!conclusionHeadWhnf.empty() && !goalHeadWhnf.empty()
            && conclusionHeadWhnf != goalHeadWhnf) {
            // Render a head for display. A term whose head is not a named
            // constant (a `∀`/`→` statement, most often) yields the
            // `<unknown>` placeholder from `headConstantName` — leaking that
            // placeholder into the message is illegible, so describe the
            // shape instead.
            auto describeHead = [&](const std::string& rawHead,
                                    const std::string& whnfHead,
                                    ExpressionPointer termForShape)
                    -> std::string {
                std::string shown =
                    rawHead.empty() ? whnfHead : rawHead;
                if (shown != "<unknown>") return "`" + shown + "`";
                ExpressionPointer reduced = termForShape
                    ? weakHeadNormalForm(environment_, termForShape)
                    : nullptr;
                if (reduced && std::get_if<Pi>(&reduced->node)) {
                    return "a `∀`/`→` statement (its head is not a named "
                           "relation)";
                }
                return "`<unknown>`";
            };
            std::string conclusionShown = describeHead(
                conclusionHeadRaw, conclusionHeadWhnf, conclusionWhnfForHeads);
            std::string goalShown =
                describeHead(goalHeadRaw, goalHeadWhnf, goalClosed);
            message +=
                "\n  its conclusion is about " + conclusionShown
                + " but the goal is about " + goalShown
                + " — this lemma does not target this goal (check the lemma "
                "name)";
        } else {
            message +=
                "\n  the conclusion shape fits, but an argument could not be "
                "inferred from the goal or a premise discharged from context — "
                "check that the goal (or an in-scope hypothesis) determines "
                "each of the lemma's arguments, or supply them explicitly";
        }
        if (!byHintFailureDetail.empty()) {
            message += "\n  " + byHintFailureDetail;
        }
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
        // Obtain-by / cases-by citations have no downstream goal to
        // validate a guessed premise against, so their discharge must be
        // unambiguous. Applies only to the citation's own call: nested
        // backward-chaining / auto-prover sub-searches run under the
        // normal first-match rules.
        bool requireUnambiguous = requireUnambiguousDischarge_
            && backwardChainingDepth_ == 0 && autoProveDepth_ == 0;
        std::string ambiguityReport;
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
            // Equality-endpoint reduction retry: the citation's conclusion
            // and the goal may spell the same endpoint through different
            // defeq wrappers (`apply(swap(a,b),a)` vs `swapMap(a,b,a)`);
            // the WHNF-both retry above only reduces the equality's TOP,
            // so the endpoint heads stay different and the structural
            // matcher can't pin the holes. Reduce each side's equality
            // ENDPOINTS to WHNF and unify again. Sound: the kernel
            // re-checks the produced term against the ORIGINAL goal.
            anyUnassigned = false;
            for (const auto& name : metavariableNames) {
                if (!assignment.count(name)) { anyUnassigned = true; break; }
            }
            if (anyUnassigned) {
                auto reduceEqualityEndpoints =
                    [&](ExpressionPointer proposition) -> ExpressionPointer {
                    if (headConstantName(proposition) != "Equality") {
                        return nullptr;
                    }
                    auto* outer =
                        std::get_if<Application>(&proposition->node);
                    if (!outer) return nullptr;
                    auto* inner =
                        std::get_if<Application>(&outer->function->node);
                    if (!inner) return nullptr;
                    ExpressionPointer leftReduced = weakHeadNormalForm(
                        environment_, inner->argument);
                    ExpressionPointer rightReduced = weakHeadNormalForm(
                        environment_, outer->argument);
                    return makeApplication(
                        makeApplication(inner->function, leftReduced),
                        rightReduced);
                };
                try {
                    ExpressionPointer patternReduced =
                        reduceEqualityEndpoints(resultTypePattern);
                    ExpressionPointer expectedReduced =
                        reduceEqualityEndpoints(expectedType);
                    if (patternReduced && expectedReduced) {
                        unifyConstructorParameters(
                            patternReduced, expectedReduced,
                            metavariableNames, assignment);
                    }
                } catch (const TypeError&) {
                    // Endpoint reduction is best-effort; fuel exhaustion
                    // just means this retry doesn't apply.
                }
            }
            // Class-equality relaxation (WS3): when the goal is
            // `mk(x) = mk(y)` but this function concludes in the underlying
            // relation `R`, unify the result pattern against `R(x, y)` so
            // the holes fill. The result then has type `R(x, y)`, and the
            // equality-of-classes coercion wraps it in Quotient.equivalent_implies_equal.
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
            // Bare-proposition-as-proof (and the other diff coercions): the
            // same treatment the constructor and plain function-call paths
            // give their arguments, so e.g. `f(?, 6 = 2 * 3)` discharges the
            // written equation via the auto-prover exactly as `f(?, proof)`
            // would. Skip when the domain still mentions an unresolved hole
            // metavariable — the coercion needs a concrete expected type, and
            // a later forward/backward step may yet pin it. WHNF first (after
            // substitution the domain is often a redex `(λx. … x …) arg`,
            // which the coercion's cheap structural prefilter would miss); it
            // no-ops when the argument already fits, leaving existing calls
            // unaffected.
            if (!containsNamedFreeVariable(expectedDomain, metavariableNames)) {
                kernelArg = coerceToExpectedTypeViaDiff(
                    localBinders, kernelArg,
                    weakHeadNormalForm(environment_, expectedDomain));
            }
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
                // Scan the local context — binders AND their conjunction legs
                // (the SAME facts the auto-prover sees, via
                // collectLocalBinderFacts) — for a proof of this side
                // condition. A hypothesis `A ∧ B` thus discharges a premise of
                // type `A` or `B` directly, projecting `And.left`/`And.right`,
                // so a `choose … such that A ∧ B`-bound condition behaves like
                // separately-stated facts.
                int N = static_cast<int>(localBinders.size());
                std::vector<ContextFact> localFacts =
                    collectLocalBinderFacts(localBinders);
                for (const ContextFact& fact : localFacts) {
                    ExpressionPointer candidateType;
                    try {
                        candidateType = openOverLocalBinders(
                            fact.type, localBinders, N);
                    } catch (const TypeError&) {
                        continue;
                    }
                    bool eq;
                    try {
                        eq = isDefinitionallyEqual(
                            environment_, openedContext,
                            candidateType, slotNormalised);
                    } catch (const TypeError&) {
                        eq = false;
                    }
                    ExpressionPointer proofForSlot = fact.proofTerm;
                    // An equality premise is direction-blind: a context
                    // fact `b = c` discharges a `c = b` slot through
                    // `Equality.symmetry`. Compare against the flipped
                    // candidate when the direct comparison fails.
                    if (!eq) {
                        ExpressionPointer flipped;
                        ExpressionPointer symmetryProof;
                        auto* outer = std::get_if<Application>(
                            &candidateType->node);
                        auto* middle = outer
                            ? std::get_if<Application>(
                                  &outer->function->node)
                            : nullptr;
                        auto* inner = middle
                            ? std::get_if<Application>(
                                  &middle->function->node)
                            : nullptr;
                        auto* head = inner
                            ? std::get_if<Constant>(&inner->function->node)
                            : nullptr;
                        if (head && head->name == "Equality") {
                            flipped = makeApplication(
                                makeApplication(
                                    makeApplication(
                                        makeConstant(
                                            "Equality",
                                            head->universeArguments),
                                        inner->argument),
                                    outer->argument),
                                middle->argument);
                            symmetryProof = makeConstant(
                                "Equality.symmetry",
                                head->universeArguments);
                            for (ExpressionPointer part :
                                     {inner->argument, middle->argument,
                                      outer->argument,
                                      openOverLocalBinders(
                                          fact.proofTerm, localBinders,
                                          N)}) {
                                symmetryProof = makeApplication(
                                    symmetryProof, part);
                            }
                        }
                        if (flipped) {
                            try {
                                eq = isDefinitionallyEqual(
                                    environment_, openedContext,
                                    flipped, slotNormalised);
                            } catch (const TypeError&) {
                                eq = false;
                            }
                            if (eq) {
                                try {
                                    proofForSlot = closeOverLocalBinders(
                                        symmetryProof, localBinders, N);
                                } catch (const TypeError&) {
                                    eq = false;
                                }
                            }
                        }
                    }
                    if (eq) {
                        elaboratedArgs[i] = proofForSlot;
                        // Diagnostic (BY_DISCHARGE_STATS): record the binder
                        // the proof bottoms out at, peeling any ∧ projections.
                        ExpressionPointer leaf = fact.proofTerm;
                        while (auto* app =
                                   std::get_if<Application>(&leaf->node)) {
                            leaf = app->argument;
                        }
                        int leafIndex = N - 1;
                        if (auto* bv =
                                std::get_if<BoundVariable>(&leaf->node)) {
                            leafIndex = bv->deBruijnIndex;
                        }
                        lastDischarges_.push_back(
                            {leafIndex, N, fact.source});
                        found = true;
                        break;
                    }
                }
                // ∀-fact instantiation: a hypothesis `∀ (x : T). P(x)`
                // (data binders, Proposition body) discharges the slot
                // `P(t)` when matching the body pins every binder — the
                // instantiation is forced by the match, so no search is
                // involved (the `termsNonneg : ∀ j. 0 ≤ s(j)` premise
                // gap). Runs after the direct scan so an exact
                // hypothesis still wins. The helper also eta-bridges
                // Pi-typed slots (`∀ j. 0 ≤ s(m + j)` from the same
                // fact, wrapped as `λ j. termsNonneg(m + j)`).
                if (!found) {
                    ExpressionPointer instantiated =
                        tryInstantiateUniversalContextFact(
                            slotType, localBinders, openedContext,
                            localFacts);
                    if (instantiated) {
                        elaboratedArgs[i] = std::move(instantiated);
                        lastDischarges_.push_back(
                            {N - 1, N, "context fact (∀-instantiated)"});
                        found = true;
                    }
                }
                if (!found) {
                    for (const ContextFact& fact : localFacts) {
                        ExpressionPointer candidateOpened;
                        try {
                            candidateOpened = openOverLocalBinders(
                                fact.type, localBinders, N);
                        } catch (const TypeError&) {
                            continue;
                        }
                        if (!factIsUniversalOverData(
                                openedContext, candidateOpened)) {
                            continue;
                        }
                        ExpressionPointer filled = nullptr;
                        try {
                            filled = autoFillHintForClaim(
                                fact.proofTerm, fact.type, slotType,
                                localBinders, line);
                        } catch (const ElaborateError&) {
                        } catch (const TypeError&) {
                        }
                        if (filled) {
                            elaboratedArgs[i] = std::move(filled);
                            lastDischarges_.push_back(
                                {N - 1, N, fact.source + " (∀-instantiated)"});
                            found = true;
                            break;
                        }
                    }
                }
                // Fallback: no direct hypothesis of this structure class, but
                // a registered forgetful instance may derive it from another
                // in-scope structure (e.g. `IsGroup` from `IsRing`).
                if (!found) {
                    ExpressionPointer derived =
                        tryForgetfulDerivation(slotType, localBinders,
                                               dischargeMetavars, assignment);
                    if (derived) {
                        elaboratedArgs[i] = std::move(derived);
                        found = true;
                    }
                }
                // Fallback 1b: a library theorem STATING the premise
                // verbatim (premise-free, matched by spine hash + defeq).
                // Search-free and prompted — the user cited this lemma —
                // so the pool is not `automatic`-gated. Skipped in the
                // speculative context scan, whose unprompted discipline
                // keeps the automatic-only pool.
                if (!found && !inSpeculativeContextScan_) {
                    ExpressionPointer stated = findPremiseFreeLibraryFact(
                        slotNormalised, slotOpened,
                        /*requireAutomatic=*/false);
                    if (stated) {
                        elaboratedArgs[i] = std::move(stated);
                        found = true;
                    }
                }
                // Fallback 2: not a stated hypothesis and no forgetful
                // instance — but the bare prover may close it
                // near-instantly from `automatic` lemmas / the tier stack
                // (`start ≤ start + c` via less_or_equal_add_right; the
                // A7 known-gap fix). Budget-capped like the redundancy
                // re-proof; skipped inside the speculative context scan,
                // where it would multiply per-candidate cost (and whose
                // flag also breaks any prover→scan→discharge recursion),
                // and for slots still mentioning unresolved holes.
                if (!found && !inSpeculativeContextScan_
                    && !containsNamedFreeVariable(slotType,
                                                  dischargeMetavars)) {
                    RedundancyBudgetGuard budgetGuard(*this);
                    ExpressionPointer proved;
                    try {
                        proved = autoProveClaim(
                            slotType, localBinders, line);
                    } catch (const ElaborateError&) {
                        proved = nullptr;
                    } catch (const TypeError&) {
                        proved = nullptr;
                    } catch (const AutoProverBudgetError&) {
                        proved = nullptr;
                    }
                    if (proved) {
                        elaboratedArgs[i] = std::move(proved);
                        found = true;
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
            // Candidate facts: local binders + their conjunction legs, shared
            // with the auto-prover and the side-condition discharge above, so
            // a premise can be unified against an `A ∧ B` hypothesis's leg.
            std::vector<ContextFact> localFacts =
                collectLocalBinderFacts(localBinders);
            // ζ-unfold map: a non-proof `let s := v` binder makes the
            // structural unifier below see `s` and `v` as different terms,
            // so a lemma premise stated over `v` (e.g. `IntegralDomain.ring
            // d`) never unifies against a hypothesis stated over the alias
            // `s` (or vice versa) — leaving the premise's holes unsolved.
            // Inline the let values into both sides before unifying.
            std::map<std::string, ExpressionPointer> letValues;
            for (size_t li = 0; li < localBinders.size(); ++li) {
                if (localBinders[li].value
                    && !localBinders[li].valueIsProof) {
                    try {
                        letValues[openingNameFor(localBinders, li)] =
                            openOverLocalBinders(
                                localBinders[li].value, localBinders, li);
                    } catch (...) {}
                }
            }
            auto zetaUnfoldOpened =
                [&](ExpressionPointer t) -> ExpressionPointer {
                if (letValues.empty()) return t;
                return substituteFreeVariables(t, letValues);
            };
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
                        slotOpened = zetaUnfoldOpened(openOverLocalBinders(
                            slotType, localBinders, N));
                    } catch (...) {
                        stillUnresolved.push_back(i); continue;
                    }
                    // No pre-Prop gate here: the slot type still carries
                    // unresolved hole FVs (the very ones we hope to solve),
                    // so it isn't yet well-formed enough to classify. We
                    // check Prop-ness AFTER unification resolves them, which
                    // preserves "never fill a value hole from context".
                    bool filled = false;
                    std::vector<size_t> matchedFacts;
                    std::map<std::string, ExpressionPointer> firstTrial;
                    auto commitMatch =
                        [&](size_t slot, const ContextFact& fact,
                            const std::map<std::string,
                                           ExpressionPointer>& solved) {
                        // Adopt the newly-solved holes (closed to the
                        // global closed-over-localBinders form) and fill
                        // this slot with the fact's proof.
                        for (const auto& entry : solved) {
                            if (assignment.count(entry.first)) continue;
                            ExpressionPointer closedValue;
                            try {
                                closedValue = closeOverLocalBinders(
                                    entry.second, localBinders, N);
                            } catch (...) { closedValue = entry.second; }
                            assignment[entry.first] = closedValue;
                        }
                        elaboratedArgs[slot] = fact.proofTerm;
                        // Diagnostic (BY_DISCHARGE_STATS): the binder the proof
                        // bottoms out at, peeling any ∧ projections.
                        ExpressionPointer leaf = fact.proofTerm;
                        while (auto* app =
                                   std::get_if<Application>(&leaf->node)) {
                            leaf = app->argument;
                        }
                        int leafIndex = N - 1;
                        if (auto* bv =
                                std::get_if<BoundVariable>(&leaf->node)) {
                            leafIndex = bv->deBruijnIndex;
                        }
                        lastDischarges_.push_back(
                            {leafIndex, N, fact.source});
                        progress = true;
                    };
                    for (size_t f = 0;
                         f < localFacts.size() && !filled; ++f) {
                        ExpressionPointer candidateType =
                            zetaUnfoldOpened(openOverLocalBinders(
                                localFacts[f].type, localBinders, N));
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
                        if (requireUnambiguous) {
                            // Collect instead of committing; resolved below
                            // once every fact has been considered.
                            if (matchedFacts.empty()) {
                                firstTrial = trial;
                                matchedFacts.push_back(f);
                            } else {
                                bool sameInstantiation = true;
                                for (auto& entry : trial) {
                                    if (assignment.count(entry.first)) {
                                        continue;
                                    }
                                    auto previous =
                                        firstTrial.find(entry.first);
                                    if (previous == firstTrial.end()
                                        || compareExpressionStructure(
                                               entry.second,
                                               previous->second) != 0) {
                                        sameInstantiation = false;
                                        break;
                                    }
                                }
                                if (!sameInstantiation) {
                                    matchedFacts.push_back(f);
                                }
                            }
                            continue;
                        }
                        commitMatch(i, localFacts[f], trial);
                        filled = true;
                    }
                    if (requireUnambiguous && !filled) {
                        if (matchedFacts.size() == 1) {
                            commitMatch(i, localFacts[matchedFacts[0]],
                                        firstTrial);
                            filled = true;
                            progress = true;
                        } else if (matchedFacts.size() > 1) {
                            ExpressionPointer slotShown;
                            try {
                                slotShown = openOverLocalBinders(
                                    substituteFreeVariables(
                                        piDomains[i], assignment),
                                    localBinders, N);
                            } catch (...) { slotShown = nullptr; }
                            auto blankHoles = [](std::string text) {
                                // Internal hole FVs print as
                                // `@_hole_<k>_<lemma>`; show `?` instead.
                                const std::string marker = "@_hole_";
                                size_t at;
                                while ((at = text.find(marker))
                                       != std::string::npos) {
                                    size_t end = at + marker.size();
                                    while (end < text.size()
                                           && (std::isalnum(
                                                   (unsigned char)text[end])
                                               || text[end] == '_'
                                               || text[end] == '.')) {
                                        ++end;
                                    }
                                    text.replace(at, end - at, "?");
                                }
                                return text;
                            };
                            ambiguityReport =
                                "ambiguous `by " + diagnosticName
                                + "` citation: the premise"
                                + (slotShown
                                       ? (" `" + blankHoles(
                                              prettyPrintInLocalScope(
                                                  slotShown, localBinders))
                                          + "`")
                                       : std::string(""))
                                + " is matched by several hypotheses that pin "
                                "different arguments:";
                            for (size_t ff : matchedFacts) {
                                ambiguityReport +=
                                    "\n    " + localFacts[ff].source + " : "
                                    + prettyPrintInLocalScope(
                                          openOverLocalBinders(
                                              localFacts[ff].type,
                                              localBinders, N),
                                          localBinders);
                            }
                            ambiguityReport +=
                                "\n  pass the lemma's arguments explicitly "
                                "to name the intended hypothesis: `"
                                + diagnosticName
                                + "(…)` (with `from` in an `obtain`).";
                        }
                    }
                    // Forgetful fallback: once the sibling hypotheses have
                    // pinned this slot's operations (no remaining holes), a
                    // structure-class slot with no matching hypothesis may be
                    // derived from another in-scope structure on the same
                    // carrier (e.g. `IsGroup` from `IsRing`). Iterated by the
                    // enclosing `while (progress)`, so a slot whose operations
                    // are pinned only on a later round is retried.
                    if (!filled) {
                        // The slot may still carry operation holes (a group's
                        // `identity`/`inverse`) that only the structure proof
                        // pins; the forgetful derivation co-solves them from
                        // the premise hypothesis and writes them back.
                        ExpressionPointer slotNow =
                            substituteFreeVariables(piDomains[i], assignment);
                        ExpressionPointer derived =
                            tryForgetfulDerivation(slotNow, localBinders,
                                                   dischargeMetavars,
                                                   assignment);
                        if (derived) {
                            elaboratedArgs[i] = std::move(derived);
                            filled = true;
                            progress = true;
                        }
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
            && ambiguityReport.empty()
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
                //
                // The depth bump MUST unwind on every exit path. This used to
                // be a bare ++/-- pair whose catch list missed
                // AutoProverBudgetError: each budget-tripped discharge attempt
                // (routine under the redundancy checker's 1000-step probes)
                // leaked one increment, and once the leaks crossed
                // kBackwardChainDepthCap (= 2) premise discharge silently shut
                // off for the REST OF THE FILE — later real citations then
                // failed with "premise could not be discharged" even though
                // they verify in isolation.
                ExpressionPointer proof = nullptr;
                ++backwardChainingDepth_;
                struct DepthDecrement {
                    int& d;
                    ~DepthDecrement() { --d; }
                } depthDecrement{backwardChainingDepth_};
                try {
                    proof = autoProveClaim(slotType, localBinders, line);
                } catch (const ElaborateError&) {
                    proof = nullptr;
                } catch (const TypeError&) {
                    proof = nullptr;
                } catch (const AutoProverBudgetError&) {
                    // A tripped budget just means this premise has no cheap
                    // discharge; the slot stays unresolved rather than
                    // aborting the whole citation.
                    proof = nullptr;
                }
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
            && ambiguityReport.empty()
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
            if (!ambiguityReport.empty()) {
                throwElaborate(ambiguityReport);
            }
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
        // `25` elaborates to one GMP-backed NaturalLiteral kernel node
        // (PLAN_FAST_NUMERALS §C) — no successor chain, no digit-count
        // ceiling. The kernel treats the literal as defeq-interchangeable
        // with the constructor form (WHNF exposes `successor`/`zero` one
        // peel at a time), so induction, pattern matching, and `decide`
        // work unchanged.
        if (environment_.lookup("Natural") == nullptr) {
            throw ElaborateError(
                "numeric literal at line " + std::to_string(line)
                + " requires Natural to be in the environment "
                "(import Natural.basics)");
        }
        (void)column;
        return makeNaturalLiteral(NaturalValue(numeric.digits));
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


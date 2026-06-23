// Out-of-line Elaborator method definitions: type/level unification, constructor-parameter inference, inferTypeInLocalContext, universe-argument inference
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

bool Elaborator::containsValueArgumentFreeVar(ExpressionPointer expression) {
        if (auto* freeVariable =
                std::get_if<FreeVariable>(&expression->node)) {
            const std::string& name = freeVariable->name;
            if (freeVariable->origin != FreeVariableOrigin::Internal) {
                return false;
            }
            static const char* placeholderPrefixes[] = {
                "_constructorValueArgument_",
                "_callTrailingArgument_",
            };
            for (const char* prefix : placeholderPrefixes) {
                size_t length = std::char_traits<char>::length(prefix);
                if (name.size() >= length
                    && name.compare(0, length, prefix) == 0) {
                    return true;
                }
            }
            return false;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return containsValueArgumentFreeVar(pi->domain)
                || containsValueArgumentFreeVar(pi->codomain);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return containsValueArgumentFreeVar(lambda->domain)
                || containsValueArgumentFreeVar(lambda->body);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return containsValueArgumentFreeVar(application->function)
                || containsValueArgumentFreeVar(application->argument);
        }
        return false;
    }

ExpressionPointer Elaborator::unfoldHeadConstantOneStep(ExpressionPointer expr) {
        std::vector<ExpressionPointer> args;
        ExpressionPointer head = expr;
        while (auto* app = std::get_if<Application>(&head->node)) {
            args.push_back(app->argument);
            head = app->function;
        }
        std::reverse(args.begin(), args.end());
        auto* constant = std::get_if<Constant>(&head->node);
        if (!constant) return nullptr;
        const Declaration* declaration =
            environment_.lookup(constant->name);
        if (!declaration) return nullptr;
        auto* definition = std::get_if<Definition>(declaration);
        if (!definition) return nullptr;
        if (definition->opacity == Opacity::Opaque) return nullptr;
        if (definition->universeParameters.size()
                != constant->universeArguments.size()) {
            return nullptr;
        }
        ExpressionPointer body = definition->body;
        if (!body) return nullptr;
        if (!definition->universeParameters.empty()) {
            body = substituteUniverseLevels(
                body, definition->universeParameters,
                constant->universeArguments);
        }
        // β-apply the spine arguments into the unfolded body.
        for (const auto& argument : args) {
            auto* lambda = std::get_if<Lambda>(&body->node);
            if (!lambda) return nullptr;
            body = substitute(lambda->body, 0, argument);
        }
        return body;
    }

void Elaborator::unifyConstructorParameters(
        ExpressionPointer pattern,
        ExpressionPointer target,
        const std::set<std::string>& metavariableNames,
        std::map<std::string, ExpressionPointer>& assignment,
        int binderDepth ,
        std::vector<ExpressionPointer>* binderTypeStack) {
        if (auto* freeVariable =
                std::get_if<FreeVariable>(&pattern->node)) {
            if (metavariableNames.count(freeVariable->name)
                && !assignment.count(freeVariable->name)
                && !containsValueArgumentFreeVar(target)
                && !referencesBoundBelowThreshold(target, binderDepth)) {
                // Lift the target up to the outer scope by shifting it
                // down by `binderDepth`. Safe because we just verified
                // the target has no references that would be captured.
                ExpressionPointer lifted = binderDepth == 0
                    ? target
                    : shift(target, -binderDepth);
                assignment[freeVariable->name] = lifted;
            }
            return;
        }
        if (auto* patternPi = std::get_if<Pi>(&pattern->node)) {
            if (auto* targetPi = std::get_if<Pi>(&target->node)) {
                unifyConstructorParameters(
                    patternPi->domain, targetPi->domain,
                    metavariableNames, assignment, binderDepth,
                    binderTypeStack);
                if (binderTypeStack)
                    binderTypeStack->push_back(patternPi->domain);
                unifyConstructorParameters(
                    patternPi->codomain, targetPi->codomain,
                    metavariableNames, assignment, binderDepth + 1,
                    binderTypeStack);
                if (binderTypeStack) binderTypeStack->pop_back();
            }
            return;
        }
        if (auto* patternLambda =
                std::get_if<Lambda>(&pattern->node)) {
            if (auto* targetLambda =
                    std::get_if<Lambda>(&target->node)) {
                unifyConstructorParameters(
                    patternLambda->domain, targetLambda->domain,
                    metavariableNames, assignment, binderDepth,
                    binderTypeStack);
                if (binderTypeStack)
                    binderTypeStack->push_back(patternLambda->domain);
                unifyConstructorParameters(
                    patternLambda->body, targetLambda->body,
                    metavariableNames, assignment, binderDepth + 1,
                    binderTypeStack);
                if (binderTypeStack) binderTypeStack->pop_back();
            }
            return;
        }
        if (auto* patternApplication =
                std::get_if<Application>(&pattern->node)) {
            ExpressionPointer patternHead = patternApplication->function;
            while (auto* nestedApp =
                       std::get_if<Application>(&patternHead->node)) {
                patternHead = nestedApp->function;
            }
            if (auto* headFreeVariable =
                    std::get_if<FreeVariable>(&patternHead->node)) {
                if (metavariableNames.count(headFreeVariable->name)) {
                    // Miller-pattern higher-order unification: if the
                    // pattern is `metavar(Bound(k))` with k < binderDepth
                    // (referring to a binder we descended into), and
                    // the target doesn't reference any DEEPER binders
                    // (those would also be captured), solve the
                    // metavariable by abstracting target over Bound(k).
                    // For now we handle only the unary case — enough for
                    // motive-style implicit predicates like
                    // `{P : T → Prop}` in `strong_induction`.
                    if (binderTypeStack
                        && !assignment.count(
                               headFreeVariable->name)) {
                        auto* singleArgBound =
                            std::get_if<BoundVariable>(
                                &patternApplication->argument->node);
                        if (singleArgBound) {
                            int k = singleArgBound->deBruijnIndex;
                            if (k >= 0 && k < binderDepth) {
                                int captureThreshold = binderDepth;
                                // Bound(k) IS allowed (we abstract it
                                // away); reject only other captures.
                                if (!referencesOtherBoundsBelowThreshold(
                                        target, captureThreshold, k)
                                    && !containsValueArgumentFreeVar(
                                           target)) {
                                    // Build Lambda(_, T_k, body) where
                                    // body abstracts over Bound(k).
                                    // T_k is the binder at depth k
                                    // from the innermost in the stack.
                                    int stackPosition =
                                        static_cast<int>(
                                            binderTypeStack->size())
                                        - 1 - k;
                                    if (stackPosition >= 0
                                        && !referencesBoundBelowThreshold(
                                               (*binderTypeStack)
                                                   [stackPosition],
                                               stackPosition)) {
                                        ExpressionPointer kType =
                                            (*binderTypeStack)
                                                [stackPosition];
                                        // The binder type was captured
                                        // in a scope with `stackPosition`
                                        // earlier descended binders.
                                        // Shift down so it lives in
                                        // the outer scope. The guard
                                        // above rejects types whose
                                        // Bound vars reference those
                                        // earlier descended binders —
                                        // those can't be expressed in
                                        // the outer scope.
                                        ExpressionPointer kTypeOuter =
                                            stackPosition == 0
                                                ? kType
                                                : shift(kType,
                                                         -stackPosition);
                                        ExpressionPointer abstracted =
                                            abstractOverBoundVariable(
                                                target, k);
                                        // `abstracted` is in scope
                                        // {outer + descended binders +
                                        //  Lambda binder}. We need it
                                        // in {outer + Lambda binder},
                                        // which means shifting indices
                                        // that reference the outer
                                        // scope (Bound(>=binderDepth+1)
                                        // after abstraction) down by
                                        // `binderDepth`, while leaving
                                        // Bound(0) (the Lambda binder)
                                        // alone. References to the
                                        // descended binders themselves
                                        // (Bound(1..binderDepth)) have
                                        // been ruled out by the
                                        // `referencesOtherBoundsBelow…`
                                        // check above.
                                        ExpressionPointer body =
                                            shift(abstracted,
                                                  -binderDepth,
                                                  binderDepth + 1);
                                        ExpressionPointer solution =
                                            makeLambda(
                                                "_motiveBinder",
                                                kTypeOuter,
                                                body);
                                        assignment[
                                            headFreeVariable->name] =
                                            solution;
                                    }
                                }
                            }
                        }
                    }
                    return;
                }
            }
            // Canonical-bundle resolution: the pattern is
            // `<Structure>.carrier(?m)` — the metavariable is the
            // projection's ARGUMENT, not its head — and the target is a
            // concrete carrier type `T`. Solve `?m` to the canonical bundle
            // registered for `(Structure, head T)`, so an implicit
            // `{r : Ring}` is recoverable from a concrete `Integer` /
            // `Polynomial(Integer, …)` operand. This never coerces a value;
            // it only supplies the unique structure bundle for a carrier,
            // and the kernel re-checks the whole application afterwards, so a
            // mis-registration cannot slip through.
            if (auto* headConstant =
                    std::get_if<Constant>(&patternHead->node)) {
                const std::string& projectionName = headConstant->name;
                const std::string suffix = ".carrier";
                bool isCarrierProjection =
                    projectionName.size() > suffix.size()
                    && projectionName.compare(
                           projectionName.size() - suffix.size(),
                           suffix.size(), suffix) == 0;
                auto* argumentFreeVariable = std::get_if<FreeVariable>(
                    &patternApplication->argument->node);
                bool singleArgument = std::holds_alternative<Constant>(
                    patternApplication->function->node);
                if (isCarrierProjection && singleArgument
                    && argumentFreeVariable
                    && metavariableNames.count(argumentFreeVariable->name)
                    && !assignment.count(argumentFreeVariable->name)) {
                    std::string structure = projectionName.substr(
                        0, projectionName.size() - suffix.size());
                    // Raw head — a defined carrier (`Integer`) WHNF-reduces
                    // to its `Quotient(…)` body, which is not how it is
                    // registered (the registry keys on the carrier as it
                    // appears in types).
                    std::string carrierHead = headConstantName(target);
                    auto entry = environment_.canonicalBundleRegistry.find(
                        std::make_tuple(structure, carrierHead));
                    if (entry != environment_.canonicalBundleRegistry.end()) {
                        assignment[argumentFreeVariable->name] =
                            makeConstant(entry->second);
                        return;
                    }
                    // Not registered: fall through to the normal matching
                    // below (no behaviour change when nothing is registered).
                }
            }
            // Walk the target's function chain to its head (a no-op when
            // the target is a bare Constant, as for a nullary alias like
            // `ComplexNumber`).
            ExpressionPointer targetHead = target;
            while (auto* nestedApp =
                       std::get_if<Application>(&targetHead->node)) {
                targetHead = nestedApp->function;
            }
            if (!headsMatch(patternHead, targetHead)) {
                // The target may be a definition/alias whose head differs
                // from the pattern's only until unfolded — e.g. pattern
                // `RingModulo(?s, ?m)` against target `FiniteField(p, f)`
                // (which δ-reduces to `RingModulo(...)`) or the nullary
                // alias `ComplexNumber` (a bare Constant that δ-reduces to
                // `RingModulo(...)`). Unfold the target one δ-step at a time
                // and retry as soon as a head aligns with the pattern's. A
                // SINGLE-step unfold (not full WHNF) is essential:
                // `RingModulo` is itself a definition for `Quotient(…)`, so
                // WHNF would blow past the `RingModulo` head we want to match
                // all the way to `Quotient`. The loop is bounded by the
                // chain of transparent definitions, so it terminates.
                ExpressionPointer current = target;
                bool matched = false;
                for (int unfoldStep = 0; unfoldStep < 64; ++unfoldStep) {
                    ExpressionPointer next =
                        unfoldHeadConstantOneStep(current);
                    if (!next) break;
                    current = next;
                    ExpressionPointer currentHead = current;
                    while (auto* nestedApp = std::get_if<Application>(
                               &currentHead->node)) {
                        currentHead = nestedApp->function;
                    }
                    if (headsMatch(patternHead, currentHead)) {
                        unifyConstructorParameters(
                            pattern, current, metavariableNames,
                            assignment, binderDepth, binderTypeStack);
                        matched = true;
                        break;
                    }
                }
                // The δ-only loop above reaches a pattern head that is a
                // transparent-definition alias (RingModulo, …) but STALLS on
                // a stuck eliminator: e.g. `Real.add(Real.zero, class_of …)`
                // δ-unfolds to a `Quotient.lift_two` whose first argument is
                // not yet a `class_of` constructor, so ι cannot fire and the
                // single-step head never becomes `class_of`. Fall back to the
                // kernel's WHNF, which performs that ι-reduction (and the δ of
                // `Real.zero` / `Real.negate` / the `(q : Real)` cast that
                // exposes the underlying `class_of`). WHNF RESPECTS opacity
                // (an opaque head is a stuck head — kernel.cpp), so it never
                // pierces an opaque definition; and because the loop above
                // has already matched any intermediate transparent alias head
                // before we reach here, this fallback cannot over-reduce past
                // a wanted alias (e.g. it cannot blow `RingModulo` past to
                // `Quotient`). If a goal makes WHNF expensive, sealing the
                // offending definition `opaque` stops it here.
                if (!matched) {
                    ExpressionPointer reduced;
                    try {
                        reduced = weakHeadNormalForm(environment_, target);
                    } catch (const KernelResourceExhausted&) {
                        reduced = nullptr;
                    }
                    if (reduced) {
                        ExpressionPointer reducedHead = reduced;
                        while (auto* nestedApp = std::get_if<Application>(
                                   &reducedHead->node)) {
                            reducedHead = nestedApp->function;
                        }
                        if (headsMatch(patternHead, reducedHead)) {
                            unifyConstructorParameters(
                                pattern, reduced, metavariableNames,
                                assignment, binderDepth, binderTypeStack);
                        }
                    }
                }
                return;
            }
            // Heads match: require the target to be an application of the
            // same arity and recurse pointwise. (A bare-Constant target
            // with a matching head has no arguments to recurse into.)
            if (auto* targetApplication =
                    std::get_if<Application>(&target->node)) {
                unifyConstructorParameters(
                    patternApplication->function,
                    targetApplication->function,
                    metavariableNames, assignment, binderDepth);
                unifyConstructorParameters(
                    patternApplication->argument,
                    targetApplication->argument,
                    metavariableNames, assignment, binderDepth);
            }
            return;
        }
    }

bool Elaborator::headsMatch(ExpressionPointer left, ExpressionPointer right) {
        if (auto* leftConstant = std::get_if<Constant>(&left->node)) {
            if (auto* rightConstant =
                    std::get_if<Constant>(&right->node)) {
                return leftConstant->name == rightConstant->name;
            }
            return false;
        }
        if (auto* leftBound = std::get_if<BoundVariable>(&left->node)) {
            if (auto* rightBound =
                    std::get_if<BoundVariable>(&right->node)) {
                return leftBound->deBruijnIndex
                    == rightBound->deBruijnIndex;
            }
            return false;
        }
        if (std::get_if<Sort>(&left->node)) {
            return std::get_if<Sort>(&right->node) != nullptr;
        }
        if (auto* leftFree = std::get_if<FreeVariable>(&left->node)) {
            if (auto* rightFree =
                    std::get_if<FreeVariable>(&right->node)) {
                return leftFree->name == rightFree->name
                    && leftFree->origin == rightFree->origin;
            }
            return false;
        }
        return false;
    }

ExpressionPointer Elaborator::inferTypeInLocalContext(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term) {
        // Precondition: `term` is CLOSED over `localBinders` (see the
        // representation-convention note above). Catch a violation here —
        // O(1) — rather than as a "bare BoundVariable" crash inside inferType.
        assertClosedOverLocalBinders(
            term, localBinders, "inferTypeInLocalContext input");
        ExpressionPointer openedTerm = openOverLocalBinders(
            term, localBinders, localBinders.size());
        Context context = buildContextFromLocalBinders(localBinders);
        return inferType(environment_, context, openedTerm);
    }

LevelPointer Elaborator::typeUniverseOf(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term) {
        ExpressionPointer typeOfTerm =
            inferTypeInLocalContext(localBinders, term);
        ExpressionPointer typeOfType =
            inferTypeInLocalContext(localBinders, typeOfTerm);
        auto* sortNode = std::get_if<Sort>(&typeOfType->node);
        if (!sortNode) {
            throw ElaborateError(
                "internal: expected a Sort when computing universe level");
        }
        LevelPointer sortLevel = sortNode->level;
        if (auto* successorLevel =
                std::get_if<LevelSuccessor>(&sortLevel->node)) {
            return successorLevel->base;
        }
        if (auto* constant = std::get_if<LevelConst>(&sortLevel->node)) {
            if (constant->value >= 1) {
                return makeLevelConst(constant->value - 1);
            }
        }
        throw ElaborateError(
            "cannot determine universe level for desugaring; the type's "
            "Sort isn't a syntactic successor — use the explicit "
            "Equality.{u}(...) form");
    }

const std::vector<std::string>& Elaborator::declarationUniverseParameters(
        const Declaration& declaration) {
        static const std::vector<std::string> empty;
        if (auto* axiom = std::get_if<Axiom>(&declaration))
            return axiom->universeParameters;
        if (auto* definition = std::get_if<Definition>(&declaration))
            return definition->universeParameters;
        if (auto* inductive = std::get_if<Inductive>(&declaration))
            return inductive->universeParameters;
        if (auto* constructor = std::get_if<Constructor>(&declaration))
            return constructor->universeParameters;
        if (auto* recursor = std::get_if<Recursor>(&declaration))
            return recursor->universeParameters;
        return empty;
    }

ExpressionPointer Elaborator::declarationType(
        const Declaration& declaration) {
        if (auto* axiom = std::get_if<Axiom>(&declaration))
            return axiom->type;
        if (auto* definition = std::get_if<Definition>(&declaration))
            return definition->type;
        if (auto* inductive = std::get_if<Inductive>(&declaration))
            return inductive->kind;
        if (auto* constructor = std::get_if<Constructor>(&declaration))
            return constructor->type;
        if (auto* recursor = std::get_if<Recursor>(&declaration))
            return recursor->type;
        return nullptr;
    }

void Elaborator::unifyLevels(
        LevelPointer expected, LevelPointer actual,
        std::map<std::string, LevelPointer>& assignment) {
        if (auto* parameter = std::get_if<LevelParam>(&expected->node)) {
            auto iterator = assignment.find(parameter->name);
            if (iterator == assignment.end()) {
                assignment[parameter->name] = actual;
            }
            return;
        }
        if (auto* expectedSuccessor =
                std::get_if<LevelSuccessor>(&expected->node)) {
            if (auto* actualSuccessor =
                    std::get_if<LevelSuccessor>(&actual->node)) {
                unifyLevels(expectedSuccessor->base,
                             actualSuccessor->base,
                             assignment);
                return;
            }
            if (auto* actualConstant =
                    std::get_if<LevelConst>(&actual->node)) {
                if (actualConstant->value >= 1) {
                    unifyLevels(expectedSuccessor->base,
                                 makeLevelConst(actualConstant->value - 1),
                                 assignment);
                    return;
                }
            }
        }
        // Other cases (max, imax, mismatched constants): no assignment.
    }

void Elaborator::unifyTypes(
        ExpressionPointer expected, ExpressionPointer actual,
        std::map<std::string, LevelPointer>& assignment) {
        // Walk Pi chains in parallel. We don't try to match Pi domains
        // (they may contain BoundVariables in the expected side that
        // don't substitute trivially); the codomain typically carries
        // the universe info we care about.
        if (auto* expectedPi = std::get_if<Pi>(&expected->node)) {
            if (auto* actualPi = std::get_if<Pi>(&actual->node)) {
                unifyTypes(expectedPi->codomain, actualPi->codomain,
                            assignment);
                return;
            }
        }
        auto* expectedSort = std::get_if<Sort>(&expected->node);
        auto* actualSort = std::get_if<Sort>(&actual->node);
        if (expectedSort && actualSort) {
            unifyLevels(expectedSort->level, actualSort->level,
                         assignment);
            return;
        }
        // Constant heads with universe-arguments lined up (e.g.,
        // Equality.{u}
        // applied to a value vs Equality.{0} applied to the same).
        if (auto* expectedConstant =
                std::get_if<Constant>(&expected->node)) {
            if (auto* actualConstant =
                    std::get_if<Constant>(&actual->node)) {
                if (expectedConstant->name == actualConstant->name) {
                    size_t commonCount = std::min(
                        expectedConstant->universeArguments.size(),
                        actualConstant->universeArguments.size());
                    for (size_t i = 0; i < commonCount; ++i) {
                        unifyLevels(
                            expectedConstant->universeArguments[i],
                            actualConstant->universeArguments[i],
                            assignment);
                    }
                }
            }
        }
        if (auto* expectedApplication =
                std::get_if<Application>(&expected->node)) {
            if (auto* actualApplication =
                    std::get_if<Application>(&actual->node)) {
                unifyTypes(expectedApplication->function,
                            actualApplication->function, assignment);
            }
        }
    }

std::vector<LevelPointer> Elaborator::inferUniverseArguments(
        const Declaration& declaration,
        const std::vector<ExpressionPointer>& valueArguments,
        const std::vector<LocalBinder>& localBinders,
        int skipLeadingPis ,
        const std::string& callSiteName ,
        bool errorOnUninferred) {

        const std::vector<std::string>& universeParameters =
            declarationUniverseParameters(declaration);
        if (universeParameters.empty()) return {};

        std::map<std::string, LevelPointer> assignment;
        ExpressionPointer cursor = declarationType(declaration);
        for (int s = 0; s < skipLeadingPis && cursor != nullptr; ++s) {
            cursor = weakHeadNormalForm(environment_, cursor);
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) { cursor = nullptr; break; }
            // Open the binder with a fresh Internal FreeVariable so the
            // codomain refers to a free name rather than a loose BVar.
            std::string skipName =
                "_inferUniverseSkip_" + std::to_string(s);
            cursor = openBinder(pi->codomain, skipName,
                                  FreeVariableOrigin::Internal);
        }
        for (size_t i = 0;
             i < valueArguments.size() && cursor != nullptr; ++i) {
            cursor = weakHeadNormalForm(environment_, cursor);
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) break;
            if (!valueArguments[i]) {
                cursor = pi->codomain;
                continue;
            }
            ExpressionPointer expectedDomain =
                weakHeadNormalForm(environment_, pi->domain);
            ExpressionPointer actualType;
            try {
                actualType = weakHeadNormalForm(environment_,
                    inferTypeInLocalContext(localBinders,
                                              valueArguments[i]));
            } catch (const TypeError&) {
                cursor = pi->codomain;
                continue;
            } catch (const ElaborateError&) {
                cursor = pi->codomain;
                continue;
            }
            unifyTypes(expectedDomain, actualType, assignment);
            cursor = pi->codomain;
        }

        std::vector<LevelPointer> result;
        int uninferredCount = 0;
        for (const auto& name : universeParameters) {
            auto iterator = assignment.find(name);
            if (iterator != assignment.end()) {
                result.push_back(iterator->second);
            } else {
                ++uninferredCount;
                result.push_back(makeLevelConst(0));
            }
        }
        // The footgun guard: a universe parameter that the argument
        // types don't pin down was historically defaulted to level 0
        // *silently*. That silently fixes a polymorphic level — fine
        // when 0 happens to be right, but otherwise it surfaces as a
        // confusing downstream type error (especially now universes are
        // non-cumulative, where a wrongly-collapsed level is rejected
        // rather than absorbed). When the caller opts in, report it
        // clearly at the call site instead, naming the fix: pass the
        // levels explicitly with `Name.{...}`.
        if (errorOnUninferred && uninferredCount > 0) {
            std::string label =
                callSiteName.empty() ? "this call" : "'" + callSiteName + "'";
            throwElaborate(
                "could not infer "
                + std::to_string(uninferredCount)
                + (uninferredCount == 1
                       ? " universe level of "
                       : " universe levels of ")
                + label
                + " from the argument types. Pass the level"
                + (uninferredCount == 1 ? "" : "s")
                + " explicitly, e.g. "
                + (callSiteName.empty() ? "Name" : callSiteName)
                + ".{0} (or .{u} to keep it polymorphic).");
        }
        return result;
    }

size_t Elaborator::universeParameterCount(const Declaration& declaration) {
        if (auto* axiom = std::get_if<Axiom>(&declaration))
            return axiom->universeParameters.size();
        if (auto* definition = std::get_if<Definition>(&declaration))
            return definition->universeParameters.size();
        if (auto* inductive = std::get_if<Inductive>(&declaration))
            return inductive->universeParameters.size();
        if (auto* constructor = std::get_if<Constructor>(&declaration))
            return constructor->universeParameters.size();
        if (auto* recursor = std::get_if<Recursor>(&declaration))
            return recursor->universeParameters.size();
        return 0;
    }


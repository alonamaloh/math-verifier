// Out-of-line Elaborator method definitions: WHNF / opaque-head forcing, deep beta reduction, and structural/defeq occurrence abstraction
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::deepWhnfThroughApplications(
        ExpressionPointer expression) {
        expression = weakHeadNormalForm(environment_, expression);
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            ExpressionPointer function =
                deepWhnfThroughApplications(application->function);
            ExpressionPointer argument =
                deepWhnfThroughApplications(application->argument);
            if (function.get() != application->function.get()
                || argument.get() != application->argument.get()) {
                return makeApplication(std::move(function),
                                        std::move(argument));
            }
        }
        return expression;
    }

bool Elaborator::mentionsOpaqueDefinition(const ExpressionPointer& expression) {
        if (auto* constant = std::get_if<Constant>(&expression->node)) {
            auto it = environment_.declarations.find(constant->name);
            if (it != environment_.declarations.end()) {
                if (auto* def = std::get_if<Definition>(&it->second);
                    def && def->opacity == Opacity::Opaque) {
                    return true;
                }
            }
            return false;
        }
        if (auto* app = std::get_if<Application>(&expression->node)) {
            return mentionsOpaqueDefinition(app->function)
                || mentionsOpaqueDefinition(app->argument);
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return mentionsOpaqueDefinition(pi->domain)
                || mentionsOpaqueDefinition(pi->codomain);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return mentionsOpaqueDefinition(lambda->domain)
                || mentionsOpaqueDefinition(lambda->body);
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return mentionsOpaqueDefinition(let->value)
                || mentionsOpaqueDefinition(let->body);
        }
        return false;
    }

const Definition* Elaborator::opaqueHeadDefinition(const ExpressionPointer& whnfed,
                                           const Constant** outConstant) {
        ExpressionPointer head = whnfed;
        while (auto* app = std::get_if<Application>(&head->node)) {
            head = app->function;
        }
        auto* constant = std::get_if<Constant>(&head->node);
        if (!constant) return nullptr;
        auto it = environment_.declarations.find(constant->name);
        if (it == environment_.declarations.end()) return nullptr;
        auto* def = std::get_if<Definition>(&it->second);
        if (!def || def->opacity != Opacity::Opaque) return nullptr;
        // Opaque is hard: never force-unfolded by the elaborator's demand-point
        // retries (deep-WHNF for `by substituting`, cases-on-expression,
        // tuple/lambda/Pi intro against an opaque type) — only `unfold X in …`.
        if (isHardOpaqueConstant(constant->name)) return nullptr;
        if (outConstant) *outConstant = constant;
        return def;
    }

ExpressionPointer Elaborator::weakHeadNormalFormForcingOpaqueHead(
            ExpressionPointer expression, int fuel) {
        while (fuel-- > 0) {
            expression = weakHeadNormalForm(environment_, expression);
            const Constant* constant = nullptr;
            const Definition* def =
                opaqueHeadDefinition(expression, &constant);
            if (!def
                || def->universeParameters.size()
                       != constant->universeArguments.size()) {
                break;
            }
            std::vector<ExpressionPointer> args;
            ExpressionPointer head = expression;
            while (auto* app = std::get_if<Application>(&head->node)) {
                args.push_back(app->argument);
                head = app->function;
            }
            std::reverse(args.begin(), args.end());
            ExpressionPointer body = def->body;
            if (!def->universeParameters.empty()) {
                body = substituteUniverseLevels(
                    body, def->universeParameters,
                    constant->universeArguments);
            }
            for (auto& a : args) body = makeApplication(body, a);
            expression = std::move(body);
        }
        return expression;
    }

ExpressionPointer Elaborator::deepWhnfForcingOpaque(
            ExpressionPointer expression,
            const std::set<std::string>& protectedDefinitions,
            int fuel) {
        if (fuel <= 0) return expression;
        expression = weakHeadNormalForm(environment_, expression);
        const Constant* constant = nullptr;
        if (const Definition* def =
                opaqueHeadDefinition(expression, &constant);
            def
            && protectedDefinitions.find(constant->name)
                   == protectedDefinitions.end()
            && def->universeParameters.size()
                   == constant->universeArguments.size()) {
            std::vector<ExpressionPointer> args;
            ExpressionPointer head = expression;
            while (auto* app = std::get_if<Application>(&head->node)) {
                args.push_back(app->argument);
                head = app->function;
            }
            std::reverse(args.begin(), args.end());
            ExpressionPointer body = def->body;
            if (!def->universeParameters.empty()) {
                body = substituteUniverseLevels(
                    body, def->universeParameters,
                    constant->universeArguments);
            }
            for (auto& a : args) body = makeApplication(body, a);
            return deepWhnfForcingOpaque(
                std::move(body), protectedDefinitions, fuel - 1);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            ExpressionPointer function = deepWhnfForcingOpaque(
                application->function, protectedDefinitions, fuel - 1);
            ExpressionPointer argument = deepWhnfForcingOpaque(
                application->argument, protectedDefinitions, fuel - 1);
            if (function.get() != application->function.get()
                || argument.get() != application->argument.get()) {
                return makeApplication(std::move(function),
                                        std::move(argument));
            }
        }
        return expression;
    }

ExpressionPointer Elaborator::deepBetaReduce(ExpressionPointer expression) {
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            ExpressionPointer function =
                deepBetaReduce(application->function);
            ExpressionPointer argument =
                deepBetaReduce(application->argument);
            if (auto* lambda = std::get_if<Lambda>(&function->node)) {
                return deepBetaReduce(
                    substitute(lambda->body, 0, argument));
            }
            return makeApplication(std::move(function),
                                    std::move(argument));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                deepBetaReduce(lambda->domain),
                deepBetaReduce(lambda->body));
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                deepBetaReduce(pi->domain),
                deepBetaReduce(pi->codomain));
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return makeLet(let->displayHint,
                deepBetaReduce(let->type),
                deepBetaReduce(let->value),
                deepBetaReduce(let->body));
        }
        return expression;
    }

bool Elaborator::expressionReferencesConstant(
        ExpressionPointer expression,
        const std::string& targetHeadName,
        std::unordered_set<std::string>& visiting) {
        if (auto* c = std::get_if<Constant>(&expression->node)) {
            if (c->name == targetHeadName) return true;
            return unfoldExposesHead(c->name, targetHeadName, visiting);
        }
        if (auto* app =
                std::get_if<Application>(&expression->node)) {
            return expressionReferencesConstant(
                       app->function, targetHeadName, visiting)
                || expressionReferencesConstant(
                       app->argument, targetHeadName, visiting);
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return expressionReferencesConstant(
                       pi->domain, targetHeadName, visiting)
                || expressionReferencesConstant(
                       pi->codomain, targetHeadName, visiting);
        }
        if (auto* lam = std::get_if<Lambda>(&expression->node)) {
            return expressionReferencesConstant(
                       lam->domain, targetHeadName, visiting)
                || expressionReferencesConstant(
                       lam->body, targetHeadName, visiting);
        }
        if (auto* letNode = std::get_if<Let>(&expression->node)) {
            return expressionReferencesConstant(
                       letNode->type, targetHeadName, visiting)
                || expressionReferencesConstant(
                       letNode->value, targetHeadName, visiting)
                || expressionReferencesConstant(
                       letNode->body, targetHeadName, visiting);
        }
        return false;
    }

bool Elaborator::unfoldExposesHead(
        const std::string& constantName,
        const std::string& targetHeadName,
        std::unordered_set<std::string>& visiting) {
        if (constantName == targetHeadName) return true;
        const std::string cacheKey =
            constantName + "|" + targetHeadName;
        auto cached = unfoldExposesHeadCache_.find(cacheKey);
        if (cached != unfoldExposesHeadCache_.end()) {
            return cached->second;
        }
        if (visiting.count(constantName)) return false;
        visiting.insert(constantName);
        bool result = false;
        const Declaration* declaration =
            environment_.lookup(constantName);
        if (declaration) {
            if (auto* def = std::get_if<Definition>(declaration)) {
                // Opaque definitions can't be δ-unfolded by WHNF, so
                // their body never gets exposed.
                if (def->opacity == Opacity::Transparent) {
                    result = expressionReferencesConstant(
                        def->body, targetHeadName, visiting);
                }
            }
        }
        visiting.erase(constantName);
        unfoldExposesHeadCache_[cacheKey] = result;
        return result;
    }

ExpressionPointer Elaborator::abstractStructuralOccurrenceWithWHNF(
        ExpressionPointer expression,
        ExpressionPointer target,
        const std::string& targetHeadName,
        int currentDepth,
        int& occurrenceCount,
        int& whnfFuel) {
        // Memoization at depth 0 (the dominant case). Keyed by raw
        // expression pointer — safe because Expression is immutable
        // and the target is fixed for one decide call. Skips the
        // recursive walk entirely on cache hit. Cache is cleared at
        // the start of each elaborateDecide.
        if (currentDepth == 0) {
            auto cached = motiveWalkerCache_.find(expression.get());
            if (cached != motiveWalkerCache_.end()) {
                occurrenceCount += cached->second.occurrenceDelta;
                whnfFuel -= cached->second.whnfFuelDelta;
                return cached->second.result;
            }
        }
        int occurrenceBefore = occurrenceCount;
        int whnfFuelBefore = whnfFuel;
        // Inner work — produces the result; the wrapper below caches
        // it (at depth 0 only) before returning.
        ExpressionPointer result =
            abstractStructuralOccurrenceWithWHNF_inner(
                expression, target, targetHeadName,
                currentDepth, occurrenceCount, whnfFuel);
        if (currentDepth == 0) {
            MotiveWalkerCacheEntry entry;
            entry.result = result;
            entry.occurrenceDelta = occurrenceCount - occurrenceBefore;
            entry.whnfFuelDelta = whnfFuelBefore - whnfFuel;
            motiveWalkerCache_[expression.get()] = std::move(entry);
        }
        return result;
    }

ExpressionPointer Elaborator::abstractStructuralOccurrenceWithWHNF_inner(
        ExpressionPointer expression,
        ExpressionPointer target,
        const std::string& targetHeadName,
        int currentDepth,
        int& occurrenceCount,
        int& whnfFuel) {
        // We can't early-stop after the first match: the motive must
        // abstract EVERY occurrence so motive(constructor) reduces
        // uniformly when the kernel ι-reduces in each arm.
        ExpressionPointer shiftedTarget =
            currentDepth == 0 ? target : shift(target, currentDepth);
        // Try structural match on the un-reduced expression first; if it
        // matches, no need to WHNF (which can be expensive and may not
        // change the head). For Application-headed expressions whose
        // head is the target's head (e.g. both are `classical_decidable`
        // applications), fall back to full definitional equality —
        // kernel WHNF often leaves the term in an intermediate form
        // (Let-binders, partial β-substitutions, recursor wrappings)
        // that doesn't match structurally but IS the same proposition.
        if (structurallyEqual(expression, shiftedTarget)) {
            occurrenceCount++;
            return makeBoundVariable(currentDepth);
        }
        if (!targetHeadName.empty()) {
            std::string thisHeadName =
                applicationHeadConstantName(expression);
            if (thisHeadName == targetHeadName) {
                // Open the local binders so isDefinitionallyEqual can
                // walk through let-binder ζ-reductions etc. The caller
                // passed expressions in closed (BoundVariable) form
                // against this localBinders scope.
                // (We use a fresh empty context since the comparison
                // is at depth `currentDepth` and the kernel's defeq
                // doesn't need extra context for closed expressions —
                // it can handle BoundVariable refs directly.)
                Context emptyContext;
                if (isDefinitionallyEqual(
                        environment_, emptyContext,
                        expression, shiftedTarget)) {
                    occurrenceCount++;
                    return makeBoundVariable(currentDepth);
                }
            }
        }
        // For Application nodes, conditionally WHNF: δ-unfolding may
        // expose the target as a subterm. Only WHNF if the head's
        // definition transitively references `targetHeadName` —
        // otherwise we'd waste fuel expanding propositional chains
        // (Real.LessOrEqual, Set.member, etc.) that can never produce
        // a `Logic.classical_decidable(…)` subterm.
        ExpressionPointer working = expression;
        if (whnfFuel > 0
            && std::get_if<Application>(&expression->node)) {
            std::string headName =
                applicationHeadConstantName(expression);
            // Always WHNF an Application whose head isn't a Constant —
            // that's a β-redex (Application of Lambda) and reducing it
            // is essentially free; if we don't, the head-relevance gate
            // never gets a chance to fire on the result. For
            // Constant-headed Applications, only WHNF if the head's
            // definition transitively references the target's head.
            bool maybeRelevant = headName.empty();
            if (!maybeRelevant && !targetHeadName.empty()) {
                std::unordered_set<std::string> visiting;
                maybeRelevant = unfoldExposesHead(
                    headName, targetHeadName, visiting);
            }
            if (maybeRelevant) {
                ExpressionPointer reduced;
                try {
                    reduced = weakHeadNormalForm(environment_, expression);
                } catch (const TypeError&) {
                    reduced = expression;
                }
                if (!structurallyEqual(reduced, expression)) {
                    whnfFuel--;
                    working = reduced;
                    if (structurallyEqual(working, shiftedTarget)) {
                        occurrenceCount++;
                        return makeBoundVariable(currentDepth);
                    }
                }
            }
        }
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&working->node)) {
            int index = boundVariable->deBruijnIndex;
            if (index >= currentDepth) {
                return makeBoundVariable(index + 1);
            }
            return working;
        }
        if (auto* pi = std::get_if<Pi>(&working->node)) {
            // The domain gets the full WHNF walk too: for an implication
            // goal the hypothesis side is a Pi DOMAIN, and the target
            // (e.g. `classical_decidable(P)` inside an unreduced
            // `filter(P, prepend(h, t))`) is only exposed by δ/ι-
            // unfolding there exactly as in the codomain. The
            // unfoldExposesHead gate keeps this cheap: domains whose
            // heads can't reach the target are never reduced.
            int before = occurrenceCount;
            ExpressionPointer newDomain =
                abstractStructuralOccurrenceWithWHNF(
                    pi->domain, target, targetHeadName,
                    currentDepth, occurrenceCount, whnfFuel);
            ExpressionPointer newCodomain =
                abstractStructuralOccurrenceWithWHNF(
                    pi->codomain, target, targetHeadName,
                    currentDepth + 1, occurrenceCount, whnfFuel);
            if (occurrenceCount == before
                && newDomain.get() == pi->domain.get()
                && newCodomain.get() == pi->codomain.get()
                && working.get() == expression.get()) {
                return expression;
            }
            return makePi(pi->displayHint,
                std::move(newDomain), std::move(newCodomain));
        }
        if (auto* lambda = std::get_if<Lambda>(&working->node)) {
            // Same domain treatment as for Pi.
            int before = occurrenceCount;
            ExpressionPointer newDomain =
                abstractStructuralOccurrenceWithWHNF(
                    lambda->domain, target, targetHeadName,
                    currentDepth, occurrenceCount, whnfFuel);
            ExpressionPointer newBody =
                abstractStructuralOccurrenceWithWHNF(
                    lambda->body, target, targetHeadName,
                    currentDepth + 1, occurrenceCount, whnfFuel);
            if (occurrenceCount == before
                && newDomain.get() == lambda->domain.get()
                && newBody.get() == lambda->body.get()
                && working.get() == expression.get()) {
                return expression;
            }
            return makeLambda(lambda->displayHint,
                std::move(newDomain), std::move(newBody));
        }
        if (auto* application =
                std::get_if<Application>(&working->node)) {
            int before = occurrenceCount;
            ExpressionPointer newFn =
                abstractStructuralOccurrenceWithWHNF(
                    application->function, target, targetHeadName,
                    currentDepth, occurrenceCount, whnfFuel);
            ExpressionPointer newArg =
                abstractStructuralOccurrenceWithWHNF(
                    application->argument, target, targetHeadName,
                    currentDepth, occurrenceCount, whnfFuel);
            if (occurrenceCount == before
                && newFn.get() == application->function.get()
                && newArg.get() == application->argument.get()
                && working.get() == expression.get()) {
                return expression;
            }
            return makeApplication(
                std::move(newFn), std::move(newArg));
        }
        if (auto* letNode = std::get_if<Let>(&working->node)) {
            // ζ-substitute the let's value into the body before
            // recursing — otherwise the body's BV(0) references to the
            // let-binder don't match the target's literal form.
            ExpressionPointer substituted = substitute(
                letNode->body, 0, letNode->value);
            return abstractStructuralOccurrenceWithWHNF(
                substituted, target, targetHeadName,
                currentDepth, occurrenceCount, whnfFuel);
        }
        return working;
    }

ExpressionPointer Elaborator::abstractDefeqOccurrence(
        ExpressionPointer expression,
        ExpressionPointer target,
        int targetArity,
        int currentDepth,
        int& occurrenceCount,
        int& defeqBudget) {
        ExpressionPointer shiftedTarget =
            currentDepth == 0 ? target : shift(target, currentDepth);
        if (structurallyEqual(expression, shiftedTarget)) {
            occurrenceCount++;
            return makeBoundVariable(currentDepth);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            // Definitional-equality attempt at a same-arity application.
            if (defeqBudget > 0) {
                int arity = 0;
                ExpressionPointer head = expression;
                while (auto* app =
                           std::get_if<Application>(&head->node)) {
                    ++arity;
                    head = app->function;
                }
                if (arity == targetArity) {
                    --defeqBudget;
                    Context emptyContext;
                    bool equal = false;
                    try {
                        equal = isDefinitionallyEqual(
                            environment_, emptyContext,
                            expression, shiftedTarget);
                    } catch (const TypeError&) {
                        equal = false;
                    }
                    if (equal) {
                        occurrenceCount++;
                        return makeBoundVariable(currentDepth);
                    }
                }
            }
            int before = occurrenceCount;
            auto newFn = abstractDefeqOccurrence(
                application->function, target, targetArity,
                currentDepth, occurrenceCount, defeqBudget);
            auto newArg = abstractDefeqOccurrence(
                application->argument, target, targetArity,
                currentDepth, occurrenceCount, defeqBudget);
            if (occurrenceCount == before
                && newFn.get() == application->function.get()
                && newArg.get() == application->argument.get()) {
                return expression;
            }
            return makeApplication(std::move(newFn), std::move(newArg));
        }
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&expression->node)) {
            int index = boundVariable->deBruijnIndex;
            if (index >= currentDepth) {
                return makeBoundVariable(index + 1);
            }
            return expression;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            int before = occurrenceCount;
            auto newDomain = abstractDefeqOccurrence(
                pi->domain, target, targetArity, currentDepth,
                occurrenceCount, defeqBudget);
            auto newCodomain = abstractDefeqOccurrence(
                pi->codomain, target, targetArity, currentDepth + 1,
                occurrenceCount, defeqBudget);
            if (occurrenceCount == before
                && newDomain.get() == pi->domain.get()
                && newCodomain.get() == pi->codomain.get()) {
                return expression;
            }
            return makePi(pi->displayHint,
                std::move(newDomain), std::move(newCodomain));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            int before = occurrenceCount;
            auto newDomain = abstractDefeqOccurrence(
                lambda->domain, target, targetArity, currentDepth,
                occurrenceCount, defeqBudget);
            auto newBody = abstractDefeqOccurrence(
                lambda->body, target, targetArity, currentDepth + 1,
                occurrenceCount, defeqBudget);
            if (occurrenceCount == before
                && newDomain.get() == lambda->domain.get()
                && newBody.get() == lambda->body.get()) {
                return expression;
            }
            return makeLambda(lambda->displayHint,
                std::move(newDomain), std::move(newBody));
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            int before = occurrenceCount;
            auto newType = abstractDefeqOccurrence(
                let->type, target, targetArity, currentDepth,
                occurrenceCount, defeqBudget);
            auto newValue = abstractDefeqOccurrence(
                let->value, target, targetArity, currentDepth,
                occurrenceCount, defeqBudget);
            auto newBody = abstractDefeqOccurrence(
                let->body, target, targetArity, currentDepth + 1,
                occurrenceCount, defeqBudget);
            if (occurrenceCount == before
                && newType.get() == let->type.get()
                && newValue.get() == let->value.get()
                && newBody.get() == let->body.get()) {
                return expression;
            }
            return makeLet(let->displayHint,
                std::move(newType), std::move(newValue),
                std::move(newBody));
        }
        return expression;
    }


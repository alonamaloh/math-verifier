// Definitions of the pure term-surgery utilities declared in the header.
#include "elaborator/term_utilities.hpp"

std::string headConstantName(const Environment& environment,
                             ExpressionPointer typeExpression) {
    ExpressionPointer cursor = typeExpression;
    while (auto* application = std::get_if<Application>(&cursor->node)) {
        cursor = application->function;
    }
    if (auto* constant = std::get_if<Constant>(&cursor->node)) {
        return constant->name;
    }
    ExpressionPointer reduced = weakHeadNormalForm(environment, typeExpression);
    while (auto* application = std::get_if<Application>(&reduced->node)) {
        reduced = weakHeadNormalForm(environment, application->function);
    }
    if (auto* constant = std::get_if<Constant>(&reduced->node)) {
        return constant->name;
    }
    return "<unknown>";
}

ExpressionPointer abstractOverBoundVariables(
    ExpressionPointer expression,
    const std::vector<int>& indices) {
    ExpressionPointer result = expression;
    for (size_t i = 0; i < indices.size(); ++i) {
        int adjustedIndex =
            indices[i] + static_cast<int>(i);
        result = abstractOverBoundVariable(result, adjustedIndex);
    }
    return result;
}

ExpressionPointer abstractOverBoundVariable(
    ExpressionPointer expression,
    int targetIndex,
    int currentDepth) {
    if (auto* boundVariable =
            std::get_if<BoundVariable>(&expression->node)) {
        int index = boundVariable->deBruijnIndex;
        int effective = index - currentDepth;
        if (effective == targetIndex) {
            return makeBoundVariable(currentDepth);
        }
        if (effective >= 0) {
            return makeBoundVariable(index + 1);
        }
        return expression;  // refers to a binder we've descended into
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
            abstractOverBoundVariable(pi->domain, targetIndex,
                                        currentDepth),
            abstractOverBoundVariable(pi->codomain, targetIndex,
                                        currentDepth + 1));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
            abstractOverBoundVariable(lambda->domain, targetIndex,
                                        currentDepth),
            abstractOverBoundVariable(lambda->body, targetIndex,
                                        currentDepth + 1));
    }
    if (auto* application =
            std::get_if<Application>(&expression->node)) {
        return makeApplication(
            abstractOverBoundVariable(application->function,
                                        targetIndex, currentDepth),
            abstractOverBoundVariable(application->argument,
                                        targetIndex, currentDepth));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return makeLet(let->displayHint,
            abstractOverBoundVariable(let->type, targetIndex,
                                        currentDepth),
            abstractOverBoundVariable(let->value, targetIndex,
                                        currentDepth),
            abstractOverBoundVariable(let->body, targetIndex,
                                        currentDepth + 1));
    }
    return expression;
}

ExpressionPointer openOverLocalBinders(
    ExpressionPointer term,
    const std::vector<LocalBinder>& localBinders,
    size_t count) {
    for (size_t i = count; i > 0; --i) {
        term = openBinder(term,
                          openingNameFor(localBinders, i - 1),
                          FreeVariableOrigin::Internal);
    }
    return term;
}

ExpressionPointer closeOverLocalBinders(
    ExpressionPointer term,
    const std::vector<LocalBinder>& localBinders,
    size_t count) {
    for (size_t i = 0; i < count; ++i) {
        term = closeBinder(term,
                            openingNameFor(localBinders, i),
                            FreeVariableOrigin::Internal);
    }
    return term;
}

bool referencesBoundBelowThreshold(ExpressionPointer expression,
                                    int threshold,
                                    int currentDepth) {
    if (auto* boundVariable =
            std::get_if<BoundVariable>(&expression->node)) {
        int effectiveIndex =
            boundVariable->deBruijnIndex - currentDepth;
        return effectiveIndex >= 0 && effectiveIndex < threshold;
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return referencesBoundBelowThreshold(pi->domain, threshold,
                                              currentDepth)
            || referencesBoundBelowThreshold(pi->codomain, threshold,
                                              currentDepth + 1);
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return referencesBoundBelowThreshold(lambda->domain, threshold,
                                              currentDepth)
            || referencesBoundBelowThreshold(lambda->body, threshold,
                                              currentDepth + 1);
    }
    if (auto* application =
            std::get_if<Application>(&expression->node)) {
        return referencesBoundBelowThreshold(
                   application->function, threshold, currentDepth)
            || referencesBoundBelowThreshold(
                   application->argument, threshold, currentDepth);
    }
    return false;
}

bool containsFreeVariable(const ExpressionPointer& expression) {
    if (!expression) return false;
    if (std::holds_alternative<FreeVariable>(expression->node)) {
        return true;
    }
    if (auto* application =
            std::get_if<Application>(&expression->node)) {
        return containsFreeVariable(application->function)
            || containsFreeVariable(application->argument);
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return containsFreeVariable(lambda->domain)
            || containsFreeVariable(lambda->body);
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return containsFreeVariable(pi->domain)
            || containsFreeVariable(pi->codomain);
    }
    return false;  // BoundVariable, Sort, Constant
}

ExpressionPointer abstractStructuralOccurrenceMasked(
    ExpressionPointer expression,
    ExpressionPointer target,
    int currentDepth,
    int& positionCounter,
    uint32_t mask) {
    ExpressionPointer shiftedTarget =
        currentDepth == 0 ? target : shift(target, currentDepth);
    if (structurallyEqual(expression, shiftedTarget)) {
        int thisIndex = positionCounter++;
        if (thisIndex < 32 && (mask & (1u << thisIndex))) {
            return makeBoundVariable(currentDepth);
        }
        // Not selected: keep the occurrence, but its bound variables must
        // still be shifted +1 (cutoff = currentDepth) to make room for the
        // motive lambda we are introducing — exactly as the plain-BV and
        // recursive cases below do. The target is NOT necessarily closed:
        // when it mentions outer binders (e.g. `gaussianProduct(coords z,
        // coords w)` with `z`, `w` bound), leaving it unshifted strands
        // those indices one level too shallow, and the later
        // `substitute(.., 0, toSide)` (which decrements every BV > 0) then
        // mangles them (z→w, w→…). Shifting here keeps every occurrence in
        // the same de Bruijn frame.
        return shift(expression, 1, currentDepth);
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
        return makePi(pi->displayHint,
            abstractStructuralOccurrenceMasked(pi->domain, target,
                currentDepth, positionCounter, mask),
            abstractStructuralOccurrenceMasked(pi->codomain, target,
                currentDepth + 1, positionCounter, mask));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
            abstractStructuralOccurrenceMasked(lambda->domain, target,
                currentDepth, positionCounter, mask),
            abstractStructuralOccurrenceMasked(lambda->body, target,
                currentDepth + 1, positionCounter, mask));
    }
    if (auto* application =
            std::get_if<Application>(&expression->node)) {
        return makeApplication(
            abstractStructuralOccurrenceMasked(application->function,
                target, currentDepth, positionCounter, mask),
            abstractStructuralOccurrenceMasked(application->argument,
                target, currentDepth, positionCounter, mask));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return makeLet(let->displayHint,
            abstractStructuralOccurrenceMasked(let->type, target,
                currentDepth, positionCounter, mask),
            abstractStructuralOccurrenceMasked(let->value, target,
                currentDepth, positionCounter, mask),
            abstractStructuralOccurrenceMasked(let->body, target,
                currentDepth + 1, positionCounter, mask));
    }
    return expression;
}

ExpressionPointer abstractStructuralOccurrence(
    ExpressionPointer expression,
    ExpressionPointer target,
    int currentDepth,
    int& occurrenceCount) {
    ExpressionPointer shiftedTarget =
        currentDepth == 0 ? target : shift(target, currentDepth);
    if (structurallyEqual(expression, shiftedTarget)) {
        occurrenceCount++;
        return makeBoundVariable(currentDepth);
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
        auto newDomain = abstractStructuralOccurrence(
            pi->domain, target, currentDepth, occurrenceCount);
        auto newCodomain = abstractStructuralOccurrence(
            pi->codomain, target, currentDepth + 1, occurrenceCount);
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
        auto newDomain = abstractStructuralOccurrence(
            lambda->domain, target, currentDepth, occurrenceCount);
        auto newBody = abstractStructuralOccurrence(
            lambda->body, target, currentDepth + 1, occurrenceCount);
        if (occurrenceCount == before
            && newDomain.get() == lambda->domain.get()
            && newBody.get() == lambda->body.get()) {
            return expression;
        }
        return makeLambda(lambda->displayHint,
            std::move(newDomain), std::move(newBody));
    }
    if (auto* application =
            std::get_if<Application>(&expression->node)) {
        int before = occurrenceCount;
        auto newFn = abstractStructuralOccurrence(
            application->function, target,
            currentDepth, occurrenceCount);
        auto newArg = abstractStructuralOccurrence(
            application->argument, target,
            currentDepth, occurrenceCount);
        if (occurrenceCount == before
            && newFn.get() == application->function.get()
            && newArg.get() == application->argument.get()) {
            return expression;
        }
        return makeApplication(
            std::move(newFn), std::move(newArg));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        int before = occurrenceCount;
        auto newType = abstractStructuralOccurrence(
            let->type, target, currentDepth, occurrenceCount);
        auto newValue = abstractStructuralOccurrence(
            let->value, target, currentDepth, occurrenceCount);
        auto newBody = abstractStructuralOccurrence(
            let->body, target, currentDepth + 1, occurrenceCount);
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
    // Sort, FreeVariable, Constant — no children, return as-is.
    return expression;
}


ExpressionPointer liftBoundVariables(
    ExpressionPointer expression, int increment, int threshold) {
    if (auto* bv =
            std::get_if<BoundVariable>(&expression->node)) {
        if (bv->deBruijnIndex >= threshold) {
            return makeBoundVariable(
                bv->deBruijnIndex + increment);
        }
        return expression;
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
            liftBoundVariables(pi->domain, increment, threshold),
            liftBoundVariables(pi->codomain, increment,
                                 threshold + 1));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
            liftBoundVariables(lambda->domain, increment, threshold),
            liftBoundVariables(lambda->body, increment,
                                 threshold + 1));
    }
    if (auto* app = std::get_if<Application>(&expression->node)) {
        return makeApplication(
            liftBoundVariables(app->function, increment, threshold),
            liftBoundVariables(app->argument, increment, threshold));
    }
    return expression;
}

int countLeadingPis(ExpressionPointer type) {
    int count = 0;
    ExpressionPointer cursor = type;
    while (auto* pi = std::get_if<Pi>(&cursor->node)) {
        ++count;
        cursor = pi->codomain;
    }
    return count;
}

size_t countExpressionNodes(ExpressionPointer e) {
    size_t total = 1;
    if (auto* app = std::get_if<Application>(&e->node)) {
        total += countExpressionNodes(app->function);
        total += countExpressionNodes(app->argument);
    } else if (auto* pi = std::get_if<Pi>(&e->node)) {
        total += countExpressionNodes(pi->domain);
        total += countExpressionNodes(pi->codomain);
    } else if (auto* lambda = std::get_if<Lambda>(&e->node)) {
        total += countExpressionNodes(lambda->domain);
        total += countExpressionNodes(lambda->body);
    } else if (auto* let = std::get_if<Let>(&e->node)) {
        total += countExpressionNodes(let->type);
        total += countExpressionNodes(let->value);
        total += countExpressionNodes(let->body);
    }
    return total;
}

std::string applicationHeadConstantName(
    ExpressionPointer expression) {
    ExpressionPointer cursor = expression;
    while (auto* app = std::get_if<Application>(&cursor->node)) {
        cursor = app->function;
    }
    if (auto* c = std::get_if<Constant>(&cursor->node)) {
        return c->name;
    }
    return std::string();
}

ExpressionPointer zetaUnfoldLetBinders(
    ExpressionPointer expression,
    const std::vector<LocalBinder>& localBinders,
    int currentDepth) {
    if (auto* boundVariable =
            std::get_if<BoundVariable>(&expression->node)) {
        int index = boundVariable->deBruijnIndex;
        if (index >= currentDepth) {
            int localOffset = index - currentDepth;
            int arrayIndex =
                static_cast<int>(localBinders.size()) - 1 - localOffset;
            if (arrayIndex >= 0
                && arrayIndex
                   < static_cast<int>(localBinders.size())
                && localBinders[arrayIndex].value) {
                // The let's value was elaborated in a scope that
                // contained the localBinders BELOW it (indices 0
                // ..arrayIndex-1) but not the ones ABOVE it. Shift
                // its BVs up by the number of binders above it
                // plus the current in-expression depth to land in
                // our scope. Recursively unfold the value too so
                // chained let-bindings collapse fully.
                // The let's value V was elaborated in a smaller
                // scope (the binders below it, size = arrayIndex).
                // Lift V to interpret its BVs in the current
                // localBinders scope; recursively unfold any
                // chained let-references it contains; then shift
                // for the in-expression depth.
                int bindersIntroducedSince =
                    static_cast<int>(localBinders.size())
                    - arrayIndex;
                ExpressionPointer valueInCurrentScope = shift(
                    localBinders[arrayIndex].value,
                    bindersIntroducedSince);
                ExpressionPointer unfolded = zetaUnfoldLetBinders(
                    valueInCurrentScope, localBinders,
                    /*currentDepth=*/0);
                return shift(unfolded, currentDepth);
            }
        }
        return expression;
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
            zetaUnfoldLetBinders(pi->domain, localBinders, currentDepth),
            zetaUnfoldLetBinders(pi->codomain, localBinders,
                                  currentDepth + 1));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
            zetaUnfoldLetBinders(lambda->domain, localBinders,
                                  currentDepth),
            zetaUnfoldLetBinders(lambda->body, localBinders,
                                  currentDepth + 1));
    }
    if (auto* application =
            std::get_if<Application>(&expression->node)) {
        return makeApplication(
            zetaUnfoldLetBinders(application->function, localBinders,
                                  currentDepth),
            zetaUnfoldLetBinders(application->argument, localBinders,
                                  currentDepth));
    }
    if (auto* letNode = std::get_if<Let>(&expression->node)) {
        return makeLet(letNode->displayHint,
            zetaUnfoldLetBinders(letNode->type, localBinders,
                                  currentDepth),
            zetaUnfoldLetBinders(letNode->value, localBinders,
                                  currentDepth),
            zetaUnfoldLetBinders(letNode->body, localBinders,
                                  currentDepth + 1));
    }
    return expression;
}

Context buildContextFromLocalBinders(
    const std::vector<LocalBinder>& localBinders) {
    Context result;
    result.reserve(localBinders.size());
    for (size_t i = 0; i < localBinders.size(); ++i) {
        ExpressionPointer openedType = openOverLocalBinders(
            localBinders[i].type, localBinders, i);
        ExpressionPointer openedValue = nullptr;
        if (localBinders[i].value) {
            openedValue = openOverLocalBinders(
                localBinders[i].value, localBinders, i);
        }
        result.push_back({openingNameFor(localBinders, i), openedType,
                          FreeVariableOrigin::Internal, openedValue});
    }
    return result;
}

ExpressionPointer substituteBoundVariable(
    ExpressionPointer body, ExpressionPointer argument, int target) {
    if (auto* bv = std::get_if<BoundVariable>(&body->node)) {
        if (bv->deBruijnIndex == target) {
            return argument;
        }
        if (bv->deBruijnIndex > target) {
            return makeBoundVariable(bv->deBruijnIndex - 1);
        }
        return body;
    }
    if (auto* app = std::get_if<Application>(&body->node)) {
        return makeApplication(
            substituteBoundVariable(app->function, argument, target),
            substituteBoundVariable(app->argument, argument, target));
    }
    if (auto* lam = std::get_if<Lambda>(&body->node)) {
        // Walk under the binder.
        // Lift `argument` by 1 because the body inside the lambda
        // has one more binding.
        ExpressionPointer argLifted =
            liftBoundVariables(argument, 1, 0);
        return makeLambda(lam->displayHint,
            substituteBoundVariable(lam->domain, argument, target),
            substituteBoundVariable(lam->body, argLifted, target + 1));
    }
    if (auto* pi = std::get_if<Pi>(&body->node)) {
        ExpressionPointer argLifted =
            liftBoundVariables(argument, 1, 0);
        return makePi(pi->displayHint,
            substituteBoundVariable(pi->domain, argument, target),
            substituteBoundVariable(pi->codomain, argLifted, target + 1));
    }
    return body;
}


ExpressionPointer zetaUnfoldLetBinders(
    ExpressionPointer term,
    const std::vector<LocalBinder>& localBinders) {
    std::map<std::string, ExpressionPointer> assignment;
    for (size_t i = 0; i < localBinders.size(); ++i) {
        if (localBinders[i].value) {
            assignment[openingNameFor(localBinders, i)] =
                openOverLocalBinders(
                    localBinders[i].value, localBinders, i);
        }
    }
    if (assignment.empty()) return term;
    ExpressionPointer opened = openOverLocalBinders(
        term, localBinders, localBinders.size());
    ExpressionPointer substituted =
        substituteFreeVariables(opened, assignment);
    return closeOverLocalBinders(
        substituted, localBinders, localBinders.size());
}

ExpressionPointer substituteFreeVariables(
    ExpressionPointer expression,
    const std::map<std::string, ExpressionPointer>& assignment,
    int binderDepth) {
    if (auto* freeVariable =
            std::get_if<FreeVariable>(&expression->node)) {
        auto iterator = assignment.find(freeVariable->name);
        if (iterator != assignment.end()) {
            return shift(iterator->second, binderDepth);
        }
        return expression;
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
            substituteFreeVariables(pi->domain, assignment,
                                      binderDepth),
            substituteFreeVariables(pi->codomain, assignment,
                                      binderDepth + 1));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
            substituteFreeVariables(lambda->domain, assignment,
                                      binderDepth),
            substituteFreeVariables(lambda->body, assignment,
                                      binderDepth + 1));
    }
    if (auto* application =
            std::get_if<Application>(&expression->node)) {
        return makeApplication(
            substituteFreeVariables(application->function, assignment,
                                      binderDepth),
            substituteFreeVariables(application->argument, assignment,
                                      binderDepth));
    }
    return expression;
}


ExpressionPointer buildEqualityTransitivity( LevelPointer universeLevel, ExpressionPointer carrierType, ExpressionPointer A, ExpressionPointer B, ExpressionPointer C, ExpressionPointer p1, ExpressionPointer p2) {
    ExpressionPointer call = makeConstant(
        "Equality.transitivity", {universeLevel});
    call = makeApplication(std::move(call), std::move(carrierType));
    call = makeApplication(std::move(call), std::move(A));
    call = makeApplication(std::move(call), std::move(B));
    call = makeApplication(std::move(call), std::move(C));
    call = makeApplication(std::move(call), std::move(p1));
    call = makeApplication(std::move(call), std::move(p2));
    return call;
}

ExpressionPointer buildEqualitySymmetry( LevelPointer universeLevel, ExpressionPointer carrierType, ExpressionPointer A, ExpressionPointer B, ExpressionPointer p) {
    ExpressionPointer call = makeConstant(
        "Equality.symmetry", {universeLevel});
    call = makeApplication(std::move(call), std::move(carrierType));
    call = makeApplication(std::move(call), std::move(A));
    call = makeApplication(std::move(call), std::move(B));
    call = makeApplication(std::move(call), std::move(p));
    return call;
}

ExpressionPointer buildEqualityCongruenceSameCarrier( LevelPointer universeLevel, ExpressionPointer carrierType, ExpressionPointer lambda, ExpressionPointer x, ExpressionPointer y, ExpressionPointer p) {
    ExpressionPointer call = makeConstant(
        "Equality.congruence",
        {universeLevel, universeLevel});
    call = makeApplication(std::move(call), carrierType);
    call = makeApplication(std::move(call), carrierType);
    call = makeApplication(std::move(call), std::move(lambda));
    call = makeApplication(std::move(call), std::move(x));
    call = makeApplication(std::move(call), std::move(y));
    call = makeApplication(std::move(call), std::move(p));
    return call;
}

ExpressionPointer buildEqualityCongruence( LevelPointer sourceUniverseLevel, ExpressionPointer sourceCarrierType, LevelPointer targetUniverseLevel, ExpressionPointer targetCarrierType, ExpressionPointer lambda, ExpressionPointer x, ExpressionPointer y, ExpressionPointer p) {
    ExpressionPointer call = makeConstant(
        "Equality.congruence",
        {sourceUniverseLevel, targetUniverseLevel});
    call = makeApplication(std::move(call), sourceCarrierType);
    call = makeApplication(std::move(call), targetCarrierType);
    call = makeApplication(std::move(call), std::move(lambda));
    call = makeApplication(std::move(call), std::move(x));
    call = makeApplication(std::move(call), std::move(y));
    call = makeApplication(std::move(call), std::move(p));
    return call;
}

ExpressionPointer buildReflexivity( LevelPointer universeLevel, ExpressionPointer carrierType, ExpressionPointer x) {
    ExpressionPointer call = makeConstant(
        "reflexivity", {universeLevel});
    call = makeApplication(std::move(call), std::move(carrierType));
    call = makeApplication(std::move(call), std::move(x));
    return call;
}

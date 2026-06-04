// Definitions of the pure term-surgery utilities declared in the header.
#include "elaborator_term_utilities.hpp"

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
        // Not selected: keep the occurrence as the original
        // expression. BVs inside the original still need shifting
        // by the surrounding lambda we'll add, but `shift` handles
        // that — except here the expression IS the target itself,
        // which is closed in the outer scope; no further BV shift
        // needed since `target` is closed (it lives in the user's
        // scope, not inside any newly-introduced lambda).
        return expression;
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


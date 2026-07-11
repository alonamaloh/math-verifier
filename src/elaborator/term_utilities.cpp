// Definitions of the pure term-surgery utilities declared in the header.
#include "elaborator/term_utilities.hpp"
#include "kernel/subtree_hash.hpp"

#include <unordered_map>

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

// Single pass of the multi-binder open: walk `term` once, replacing each
// BoundVariable that refers to one of the `count` opened binders with the
// corresponding FreeVariable, and shifting the rest down by `count`. This is
// the fused equivalent of calling openBinder `count` times in a row (which
// would walk the term `count` times). `freeVars[k]` is the FreeVariable for
// local-binder index k; they are closed, so no per-depth shifting is needed.
// Mirrors substitute's depth tracking and structural-sharing fast path, so
// the result is pointer-identical to the iterated version (FreeVariables are
// interned).
static ExpressionPointer openManyBindersPass(
    ExpressionPointer expression,
    const std::vector<ExpressionPointer>& freeVars,
    int depth) {
    const int count = static_cast<int>(freeVars.size());
    // No free BoundVariable reaches the opened binders here — unchanged.
    if (expression->maxFreeBoundVariable < depth) return expression;
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        int effective = boundVariable->deBruijnIndex - depth;
        if (effective < 0) return expression;
        if (effective < count) return freeVars[count - 1 - effective];
        return makeBoundVariable(boundVariable->deBruijnIndex - count);
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        auto newDomain = openManyBindersPass(pi->domain, freeVars, depth);
        auto newCodomain =
            openManyBindersPass(pi->codomain, freeVars, depth + 1);
        if (newDomain == pi->domain && newCodomain == pi->codomain) {
            return expression;
        }
        return makePi(pi->displayHint, std::move(newDomain),
                      std::move(newCodomain));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        auto newDomain = openManyBindersPass(lambda->domain, freeVars, depth);
        auto newBody = openManyBindersPass(lambda->body, freeVars, depth + 1);
        if (newDomain == lambda->domain && newBody == lambda->body) {
            return expression;
        }
        return makeLambda(lambda->displayHint, std::move(newDomain),
                          std::move(newBody));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        auto newFunction =
            openManyBindersPass(application->function, freeVars, depth);
        auto newArgument =
            openManyBindersPass(application->argument, freeVars, depth);
        if (newFunction == application->function
            && newArgument == application->argument) {
            return expression;
        }
        return makeApplication(std::move(newFunction),
                               std::move(newArgument));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        auto newType = openManyBindersPass(let->type, freeVars, depth);
        auto newValue = openManyBindersPass(let->value, freeVars, depth);
        auto newBody = openManyBindersPass(let->body, freeVars, depth + 1);
        if (newType == let->type && newValue == let->value
            && newBody == let->body) {
            return expression;
        }
        return makeLet(let->displayHint, std::move(newType),
                       std::move(newValue), std::move(newBody));
    }
    return expression;  // FreeVariable, Sort, Constant
}

ExpressionPointer openOverLocalBinders(
    ExpressionPointer term,
    const std::vector<LocalBinder>& localBinders,
    size_t count) {
    if (count == 0) return term;
    std::vector<ExpressionPointer> freeVars;
    freeVars.reserve(count);
    for (size_t k = 0; k < count; ++k) {
        freeVars.push_back(openedLocalBinderReference(localBinders, k));
    }
    return openManyBindersPass(std::move(term), freeVars, 0);
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

ExpressionPointer openedLocalBinderReference(
    const std::vector<LocalBinder>& localBinders, size_t index) {
    // Mirror the Internal-origin FreeVariable that openBinder constructs (same
    // name + origin + hash), so this term is structurally identical to the one
    // openOverLocalBinders produces for this binder.
    const std::string name = openingNameFor(localBinders, index);
    uint64_t nameHash = subtree_hash::hashString(name);
    auto freeVar = makeRawExpression(
        FreeVariable{name, FreeVariableOrigin::Internal});
    freeVar->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagFreeVariable),
            nameHash),
        static_cast<uint64_t>(FreeVariableOrigin::Internal));
    return freeVar;
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
    uint32_t mask,
    const StructuralNodeMatcher* nodeMatches) {
    ExpressionPointer shiftedTarget =
        currentDepth == 0 ? target : shift(target, currentDepth);
    if (structurallyEqual(expression, shiftedTarget)
        || (nodeMatches && *nodeMatches
            && (*nodeMatches)(expression, shiftedTarget))) {
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
    // Recursive cases sequence the sub-calls into named locals before
    // passing to make*: each sub-call mutates `positionCounter`, and
    // function-argument evaluation order is unspecified in C++ — passing
    // them directly would let the compiler reorder, swapping the
    // position indices between children and breaking the mask.
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        auto newDomain = abstractStructuralOccurrenceMasked(
            pi->domain, target, currentDepth, positionCounter, mask,
            nodeMatches);
        auto newCodomain = abstractStructuralOccurrenceMasked(
            pi->codomain, target, currentDepth + 1, positionCounter, mask,
            nodeMatches);
        return makePi(pi->displayHint,
            std::move(newDomain), std::move(newCodomain));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        auto newDomain = abstractStructuralOccurrenceMasked(
            lambda->domain, target, currentDepth, positionCounter, mask,
            nodeMatches);
        auto newBody = abstractStructuralOccurrenceMasked(
            lambda->body, target, currentDepth + 1, positionCounter, mask,
            nodeMatches);
        return makeLambda(lambda->displayHint,
            std::move(newDomain), std::move(newBody));
    }
    if (auto* application =
            std::get_if<Application>(&expression->node)) {
        auto newFn = abstractStructuralOccurrenceMasked(
            application->function, target, currentDepth,
            positionCounter, mask, nodeMatches);
        auto newArg = abstractStructuralOccurrenceMasked(
            application->argument, target, currentDepth,
            positionCounter, mask, nodeMatches);
        return makeApplication(std::move(newFn), std::move(newArg));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        auto newType = abstractStructuralOccurrenceMasked(
            let->type, target, currentDepth, positionCounter, mask,
            nodeMatches);
        auto newValue = abstractStructuralOccurrenceMasked(
            let->value, target, currentDepth, positionCounter, mask,
            nodeMatches);
        auto newBody = abstractStructuralOccurrenceMasked(
            let->body, target, currentDepth + 1, positionCounter, mask,
            nodeMatches);
        return makeLet(let->displayHint,
            std::move(newType), std::move(newValue), std::move(newBody));
    }
    return expression;
}

ExpressionPointer abstractStructuralOccurrence(
    ExpressionPointer expression,
    ExpressionPointer target,
    int currentDepth,
    int& occurrenceCount,
    const StructuralNodeMatcher* nodeMatches) {
    ExpressionPointer shiftedTarget =
        currentDepth == 0 ? target : shift(target, currentDepth);
    if (structurallyEqual(expression, shiftedTarget)
        || (nodeMatches && *nodeMatches
            && (*nodeMatches)(expression, shiftedTarget))) {
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
            pi->domain, target, currentDepth, occurrenceCount, nodeMatches);
        auto newCodomain = abstractStructuralOccurrence(
            pi->codomain, target, currentDepth + 1, occurrenceCount,
            nodeMatches);
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
            lambda->domain, target, currentDepth, occurrenceCount,
            nodeMatches);
        auto newBody = abstractStructuralOccurrence(
            lambda->body, target, currentDepth + 1, occurrenceCount,
            nodeMatches);
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
            currentDepth, occurrenceCount, nodeMatches);
        auto newArg = abstractStructuralOccurrence(
            application->argument, target,
            currentDepth, occurrenceCount, nodeMatches);
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
            let->type, target, currentDepth, occurrenceCount, nodeMatches);
        auto newValue = abstractStructuralOccurrence(
            let->value, target, currentDepth, occurrenceCount, nodeMatches);
        auto newBody = abstractStructuralOccurrence(
            let->body, target, currentDepth + 1, occurrenceCount,
            nodeMatches);
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
    if (auto* let = std::get_if<Let>(&expression->node)) {
        // A ζ-let binds one variable for its body — the body's threshold
        // shifts by one, like a lambda. (Missing this case silently left
        // free variables under `let` unlifted — the 3-arm `by cases`
        // fold's misapplied-type kernel error.)
        return makeLet(let->displayHint,
            liftBoundVariables(let->type, increment, threshold),
            liftBoundVariables(let->value, increment, threshold),
            liftBoundVariables(let->body, increment, threshold + 1));
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
    // Memoized: this is a pure function of `localBinders`, but it is called
    // O(claims) times per proof with a slowly-growing binder list, and each
    // build opens every binder against all lower ones — O(N^2) substitutions,
    // the dominant elaboration cost on big proofs (e.g. Real.derivative's
    // `multiply`). The opened context is identical whenever the binder
    // signature (per-binder name + type + value + valueIsProof) matches.
    // Expression pointers are interned, so pointer identity == structural
    // identity; we keep the input binders alive in the cache entry, so an
    // address can never be recycled to a different expression (soundness).
    struct CacheEntry {
        std::vector<LocalBinder> signature;  // keeps inputs alive + exact check
        Context context;
    };
    static thread_local std::unordered_map<uint64_t, CacheEntry> cache;
    uint64_t key = subtree_hash::kSeed;
    for (const LocalBinder& binder : localBinders) {
        key = subtree_hash::mix(key, subtree_hash::hashString(binder.name));
        key = subtree_hash::mix(key, binder.type ? binder.type->hash : 0);
        key = subtree_hash::mix(key, binder.value ? binder.value->hash : 0);
        key = subtree_hash::mix(key, binder.valueIsProof ? 1u : 0u);
    }
    auto cached = cache.find(key);
    if (cached != cache.end()) {
        const std::vector<LocalBinder>& signature = cached->second.signature;
        bool match = signature.size() == localBinders.size();
        for (size_t i = 0; match && i < signature.size(); ++i) {
            match = signature[i].name == localBinders[i].name
                && signature[i].type.get() == localBinders[i].type.get()
                && signature[i].value.get() == localBinders[i].value.get()
                && signature[i].valueIsProof == localBinders[i].valueIsProof;
        }
        if (match) return cached->second.context;
    }
    Context result;
    result.reserve(localBinders.size());
    for (size_t i = 0; i < localBinders.size(); ++i) {
        ExpressionPointer openedType = openOverLocalBinders(
            localBinders[i].type, localBinders, i);
        ExpressionPointer openedValue = nullptr;
        // Proof-valued lets are omitted from the kernel context: ζ-
        // substituting a proof term can never decide a type-level defeq,
        // and carrying it makes every isDefinitionallyEqual under the
        // binder pay an O(proof-size) substitution on both query sides
        // (see LocalBinder::valueIsProof).
        if (localBinders[i].value && !localBinders[i].valueIsProof) {
            openedValue = openOverLocalBinders(
                localBinders[i].value, localBinders, i);
        }
        result.push_back({openingNameFor(localBinders, i), openedType,
                          FreeVariableOrigin::Internal, openedValue});
    }
    // Bound to keep memory in check on pathological runs; the working set of
    // distinct contexts in a single file is far smaller.
    if (cache.size() > 100000) cache.clear();
    cache.insert_or_assign(key, CacheEntry{localBinders, result});
    return result;
}

ExpressionPointer replaceBoundVariableInPlace(
    ExpressionPointer body, int target, ExpressionPointer replacement) {
    if (auto* bv = std::get_if<BoundVariable>(&body->node)) {
        if (bv->deBruijnIndex == target) {
            return replacement;
        }
        return body;  // indices unchanged — the binder stays.
    }
    if (auto* app = std::get_if<Application>(&body->node)) {
        return makeApplication(
            replaceBoundVariableInPlace(app->function, target, replacement),
            replaceBoundVariableInPlace(app->argument, target, replacement));
    }
    if (auto* lam = std::get_if<Lambda>(&body->node)) {
        ExpressionPointer replacementLifted =
            liftBoundVariables(replacement, 1, 0);
        return makeLambda(lam->displayHint,
            replaceBoundVariableInPlace(lam->domain, target, replacement),
            replaceBoundVariableInPlace(
                lam->body, target + 1, replacementLifted));
    }
    if (auto* pi = std::get_if<Pi>(&body->node)) {
        ExpressionPointer replacementLifted =
            liftBoundVariables(replacement, 1, 0);
        return makePi(pi->displayHint,
            replaceBoundVariableInPlace(pi->domain, target, replacement),
            replaceBoundVariableInPlace(
                pi->codomain, target + 1, replacementLifted));
    }
    if (auto* let = std::get_if<Let>(&body->node)) {
        ExpressionPointer replacementLifted =
            liftBoundVariables(replacement, 1, 0);
        return makeLet(let->displayHint,
            replaceBoundVariableInPlace(let->type, target, replacement),
            replaceBoundVariableInPlace(let->value, target, replacement),
            replaceBoundVariableInPlace(
                let->body, target + 1, replacementLifted));
    }
    return body;
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


// Read-only test: does `term` (closed over `localBinders`) contain any
// BoundVariable resolving to a let-valued binder? When it does not,
// ζ-unfolding is a no-op, so the caller can skip the open/substitute/close
// round-trip entirely (three allocating tree walks on what may be a large
// goal). Mirrors the BoundVariable-resolution arithmetic in the recursive
// `zetaUnfoldLetBinders` below, but allocates nothing.
static bool referencesLetValuedBinder(
    ExpressionPointer expression,
    const std::vector<LocalBinder>& localBinders,
    int currentDepth) {
    if (auto* boundVariable =
            std::get_if<BoundVariable>(&expression->node)) {
        int index = boundVariable->deBruijnIndex;
        if (index >= currentDepth) {
            int arrayIndex = static_cast<int>(localBinders.size())
                - 1 - (index - currentDepth);
            if (arrayIndex >= 0
                && arrayIndex < static_cast<int>(localBinders.size())
                && localBinders[arrayIndex].value) {
                return true;
            }
        }
        return false;
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return referencesLetValuedBinder(pi->domain, localBinders, currentDepth)
            || referencesLetValuedBinder(pi->codomain, localBinders,
                                          currentDepth + 1);
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return referencesLetValuedBinder(lambda->domain, localBinders,
                                          currentDepth)
            || referencesLetValuedBinder(lambda->body, localBinders,
                                          currentDepth + 1);
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return referencesLetValuedBinder(application->function, localBinders,
                                          currentDepth)
            || referencesLetValuedBinder(application->argument, localBinders,
                                          currentDepth);
    }
    if (auto* letNode = std::get_if<Let>(&expression->node)) {
        return referencesLetValuedBinder(letNode->type, localBinders,
                                          currentDepth)
            || referencesLetValuedBinder(letNode->value, localBinders,
                                          currentDepth)
            || referencesLetValuedBinder(letNode->body, localBinders,
                                          currentDepth + 1);
    }
    return false;
}

namespace {
// FreeVariable-name → opened-value assignment for every value-carrying
// binder, shared by the closed- and opened-form ζ-unfold entry points.
std::map<std::string, ExpressionPointer> letValueAssignment(
    const std::vector<LocalBinder>& localBinders) {
    std::map<std::string, ExpressionPointer> assignment;
    for (size_t i = 0; i < localBinders.size(); ++i) {
        if (localBinders[i].value) {
            assignment[openingNameFor(localBinders, i)] =
                openOverLocalBinders(
                    localBinders[i].value, localBinders, i);
        }
    }
    return assignment;
}
} // namespace

ExpressionPointer zetaUnfoldLetBinders(
    ExpressionPointer term,
    const std::vector<LocalBinder>& localBinders) {
    // Fast path: if `term` references no let-valued binder, ζ-unfolding
    // cannot change it. One read-only walk replaces the three allocating
    // tree copies (open/substitute/close) below — the dominant cost when
    // the auto-prover's context-fact scan ζ-probes the (unchanged) goal
    // against many candidate hints.
    if (!referencesLetValuedBinder(term, localBinders, 0)) return term;
    std::map<std::string, ExpressionPointer> assignment =
        letValueAssignment(localBinders);
    if (assignment.empty()) return term;
    ExpressionPointer opened = openOverLocalBinders(
        term, localBinders, localBinders.size());
    // To fixpoint: a let's value may itself reference an earlier let
    // (`let gTolerance := ε / 2 / fRoof` with `let fRoof := …`), and
    // substituteFreeVariables does not re-scan the substituted values.
    // Each pass eliminates one let layer; lets cannot be cyclic, so
    // this terminates within |localBinders| passes.
    for (size_t pass = 0; pass < localBinders.size(); ++pass) {
        ExpressionPointer substituted =
            substituteFreeVariables(opened, assignment);
        if (substituted == opened) break;
        opened = substituted;
    }
    return closeOverLocalBinders(
        opened, localBinders, localBinders.size());
}

ExpressionPointer zetaUnfoldLetBindersOpened(
    ExpressionPointer term,
    const std::vector<LocalBinder>& localBinders) {
    std::map<std::string, ExpressionPointer> assignment =
        letValueAssignment(localBinders);
    if (assignment.empty()) return term;
    // Same fixpoint discipline as the closed-form entry point above.
    for (size_t pass = 0; pass < localBinders.size(); ++pass) {
        ExpressionPointer substituted =
            substituteFreeVariables(term, assignment);
        if (substituted == term) break;
        term = substituted;
    }
    return term;
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

// Out-of-line Elaborator method definitions: the rewrite and simplify tactics (desugarRewrite, pattern instantiation, first-order match, simplify).
// The surface `rewrite(…)` spelling is RETIRED (dispatch.cpp throws the
// migration error); desugarRewrite survives as the internal citation-parity
// fallback (calc.cpp, inference.cpp).
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::desugarRewrite(
        SurfaceExpressionPointer lemmaSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "rewrite at line " + std::to_string(line));
        TimedScope _scope(*this, "desugarRewrite");
        if (!expectedType) {
            throwElaborate(
                "rewrite needs an expected type from context — use it "
                "in a calc step, where the step's `previous = next` "
                "equality provides the target");
        }
        // The 1-arg rewrite wraps via Equality.congruence. If that name
        // isn't declared (small test modules sometimes omit it), bail
        // out so the caller can fall through to its own diagnostic,
        // rather than handing the kernel a term that mentions an
        // undefined constant.
        if (!environment_.lookup("Equality.congruence")) {
            throwElaborate(
                "rewrite: Equality.congruence is not declared in "
                "scope; cannot synthesise the calc-step congruence "
                "wrap");
        }
        EqualityComponents goalComponents =
            extractEqualityComponents(expectedType, "rewrite (goal)", line);

        // Elaborate the lemma; close its inferred type's components back
        // to BoundVariables so they live in the same scope as
        // `expectedType` (which arrived in closed form).
        ExpressionPointer lemmaKernel =
            elaborateExpression(*lemmaSurface, localBinders);
        ExpressionPointer lemmaTypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, lemmaKernel));
        EqualityComponents lemmaComponentsOpened =
            extractEqualityComponents(lemmaTypeOpened, "rewrite (lemma)",
                                       line);
        ExpressionPointer lemmaCarrier = closeOverLocalBinders(
            lemmaComponentsOpened.carrierType,
            localBinders, localBinders.size());
        ExpressionPointer lemmaLeft = closeOverLocalBinders(
            lemmaComponentsOpened.leftEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer lemmaRight = closeOverLocalBinders(
            lemmaComponentsOpened.rightEndpoint,
            localBinders, localBinders.size());

        // Locate the unique occurrence of `lemmaLeft` inside the goal's
        // left endpoint, replacing it with BoundVariable(0) and shifting
        // outer references up by 1. If the forward direction doesn't
        // find a match, automatically try the reverse direction (as if
        // the user wrote `rewrite(Equality.symmetry(lemma))`).
        int occurrenceCount = 0;
        ExpressionPointer abstractedBody = abstractStructuralOccurrence(
            goalComponents.leftEndpoint, lemmaLeft,
            /*currentDepth=*/0, occurrenceCount);
        bool reversed = false;
        if (occurrenceCount == 0) {
            int reverseOccurrenceCount = 0;
            ExpressionPointer reverseAbstractedBody =
                abstractStructuralOccurrence(
                    goalComponents.leftEndpoint, lemmaRight,
                    /*currentDepth=*/0, reverseOccurrenceCount);
            if (reverseOccurrenceCount > 0) {
                occurrenceCount = reverseOccurrenceCount;
                abstractedBody = std::move(reverseAbstractedBody);
                reversed = true;
            } else {
                throwElaborate(
                    "rewrite: neither endpoint of the lemma appears "
                    "(structurally) in the goal's left side");
            }
        }
        if (occurrenceCount > 1) {
            throwElaborate(
                "rewrite: the lemma's left endpoint appears "
                + std::to_string(occurrenceCount)
                + " times in the goal's left side — use explicit "
                "`congruenceOf(function (z) => …, lemma)` to "
                "disambiguate the position");
        }
        ExpressionPointer abstractionLambda = makeLambda(
            "_rewriteHole", lemmaCarrier, abstractedBody);

        // Build `Equality.congruence.{u, v}(lemmaT, goalT, λ,
        //                                    lemmaLeft, lemmaRight,
        //                                    lemma)`.
        // When reversed, swap the endpoints and wrap the lemma in
        // Equality.symmetry so the resulting term still type-checks.
        ExpressionPointer effectiveLemma = lemmaKernel;
        ExpressionPointer effectiveLeft = lemmaLeft;
        ExpressionPointer effectiveRight = lemmaRight;
        if (reversed) {
            ExpressionPointer symmetryCall = makeConstant(
                "Equality.symmetry",
                {lemmaComponentsOpened.carrierUniverseLevel});
            symmetryCall = makeApplication(
                std::move(symmetryCall), lemmaCarrier);
            symmetryCall = makeApplication(
                std::move(symmetryCall), lemmaLeft);
            symmetryCall = makeApplication(
                std::move(symmetryCall), lemmaRight);
            symmetryCall = makeApplication(
                std::move(symmetryCall), std::move(effectiveLemma));
            effectiveLemma = std::move(symmetryCall);
            std::swap(effectiveLeft, effectiveRight);
        }
        ExpressionPointer call = makeConstant(
            "Equality.congruence",
            {lemmaComponentsOpened.carrierUniverseLevel,
             goalComponents.carrierUniverseLevel});
        call = makeApplication(std::move(call), lemmaCarrier);
        call = makeApplication(std::move(call), goalComponents.carrierType);
        call = makeApplication(std::move(call), std::move(abstractionLambda));
        call = makeApplication(std::move(call), std::move(effectiveLeft));
        call = makeApplication(std::move(call), std::move(effectiveRight));
        call = makeApplication(std::move(call), std::move(effectiveLemma));
        return call;
    }

bool Elaborator::tryFirstOrderMatch(
        ExpressionPointer pattern,
        ExpressionPointer term,
        int numPatternBinders,
        std::vector<ExpressionPointer>& bindings) {
        if (auto* boundVar =
                std::get_if<BoundVariable>(&pattern->node)) {
            int idx = boundVar->deBruijnIndex;
            if (idx < numPatternBinders) {
                if (bindings[idx]) {
                    return structurallyEqual(bindings[idx], term);
                }
                bindings[idx] = term;
                return true;
            }
            // Reference outside the lemma's universal quantifiers — must
            // be a literal match against an outer BoundVariable in the
            // term (after adjusting for the binder offset).
            auto* termVar =
                std::get_if<BoundVariable>(&term->node);
            if (!termVar) return false;
            return termVar->deBruijnIndex == idx - numPatternBinders;
        }
        if (auto* application =
                std::get_if<Application>(&pattern->node)) {
            auto* termApp =
                std::get_if<Application>(&term->node);
            if (!termApp) return false;
            return tryFirstOrderMatch(application->function,
                                       termApp->function,
                                       numPatternBinders, bindings)
                && tryFirstOrderMatch(application->argument,
                                       termApp->argument,
                                       numPatternBinders, bindings);
        }
        if (std::get_if<Constant>(&pattern->node)
            || std::get_if<Sort>(&pattern->node)
            || std::get_if<FreeVariable>(&pattern->node)) {
            return structurallyEqual(pattern, term);
        }
        // Pi/Lambda/Let — matching does not descend under binders.
        return false;
    }

ExpressionPointer Elaborator::instantiatePattern(
        ExpressionPointer pattern,
        const std::vector<ExpressionPointer>& bindings,
        int numPatternBinders,
        int currentDepth) {
        if (auto* boundVar =
                std::get_if<BoundVariable>(&pattern->node)) {
            int idx = boundVar->deBruijnIndex;
            if (idx < currentDepth) {
                return pattern;  // bound locally inside the pattern
            }
            int effective = idx - currentDepth;
            if (effective < numPatternBinders) {
                ExpressionPointer binding = bindings[effective];
                if (currentDepth > 0) {
                    binding = shift(binding, currentDepth);
                }
                return binding;
            }
            return makeBoundVariable(
                idx - numPatternBinders);
        }
        if (auto* application =
                std::get_if<Application>(&pattern->node)) {
            return makeApplication(
                instantiatePattern(application->function, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(application->argument, bindings,
                                    numPatternBinders, currentDepth));
        }
        if (auto* pi = std::get_if<Pi>(&pattern->node)) {
            return makePi(pi->displayHint,
                instantiatePattern(pi->domain, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(pi->codomain, bindings,
                                    numPatternBinders, currentDepth + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&pattern->node)) {
            return makeLambda(lambda->displayHint,
                instantiatePattern(lambda->domain, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(lambda->body, bindings,
                                    numPatternBinders, currentDepth + 1));
        }
        if (auto* let = std::get_if<Let>(&pattern->node)) {
            return makeLet(let->displayHint,
                instantiatePattern(let->type, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(let->value, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(let->body, bindings,
                                    numPatternBinders, currentDepth + 1));
        }
        // Constant / Sort / FreeVariable — pure leaves.
        return pattern;
    }

bool Elaborator::findFirstSimplifyMatch(
        ExpressionPointer term,
        const std::vector<SimplifyLemma>& lemmas,
        size_t& matchedLemmaIndex,
        std::vector<ExpressionPointer>& bindings,
        ExpressionPointer& matchedSubterm) {
        for (size_t i = 0; i < lemmas.size(); ++i) {
            std::vector<ExpressionPointer> attempt(
                lemmas[i].numBinders, nullptr);
            if (tryFirstOrderMatch(lemmas[i].leftPattern, term,
                                    lemmas[i].numBinders, attempt)) {
                bool complete = true;
                for (const auto& b : attempt) {
                    if (!b) { complete = false; break; }
                }
                if (complete) {
                    matchedLemmaIndex = i;
                    bindings = std::move(attempt);
                    matchedSubterm = term;
                    return true;
                }
            }
        }
        if (auto* application =
                std::get_if<Application>(&term->node)) {
            if (findFirstSimplifyMatch(application->function, lemmas,
                                         matchedLemmaIndex, bindings,
                                         matchedSubterm)) {
                return true;
            }
            return findFirstSimplifyMatch(application->argument, lemmas,
                                            matchedLemmaIndex, bindings,
                                            matchedSubterm);
        }
        // Don't descend into Pi/Lambda/Let bodies — the captured
        // binders would make any match references invalid in the outer
        // proof. Constants/Sorts/Bound/FreeVariable are leaves.
        return false;
    }

ExpressionPointer Elaborator::buildSingleSimplifyStep(
        const SimplifyLemma& lemma,
        const std::vector<ExpressionPointer>& bindings,
        ExpressionPointer current,
        ExpressionPointer matchedSubterm,
        ExpressionPointer newCurrent,
        ExpressionPointer goalCarrier,
        LevelPointer goalCarrierUniverseLevel,
        ExpressionPointer instantiatedRight) {
        // Instantiated lemma value: lemma applied to each bound argument
        // in declaration order.
        ExpressionPointer instantiatedLemma = lemma.lemmaReference;
        for (int i = lemma.numBinders - 1; i >= 0; --i) {
            instantiatedLemma = makeApplication(
                std::move(instantiatedLemma), bindings[i]);
        }
        ExpressionPointer instantiatedCarrier =
            instantiatePattern(lemma.carrier, bindings,
                                lemma.numBinders);
        // Abstract the matched subterm out of `current`, building the
        // motive lambda for Equality.congruence.
        int occurrenceCount = 0;
        ExpressionPointer abstractedBody = abstractStructuralOccurrence(
            current, matchedSubterm, 0, occurrenceCount);
        if (occurrenceCount == 0) {
            throw ElaborateError(
                "simplify: internal — matched subterm not located "
                "structurally after match");
        }
        // Multiple matches: rewrite still produces a valid proof
        // (Equality.congruence will replace every Bound(0) in the
        // motive simultaneously), so we don't need to fail here.
        ExpressionPointer motiveLambda = makeLambda(
            "_simplifyHole", instantiatedCarrier,
            std::move(abstractedBody));
        // Equality.congruence's `x` and `y` are the lemma's endpoints
        // (matchedSubterm and instantiatedRight). The motive carries
        // the surrounding context: `motive(x) = matchedSubterm`-shaped
        // = current; `motive(y) = instantiatedRight`-shaped = newCurrent.
        ExpressionPointer call = makeConstant(
            "Equality.congruence",
            {lemma.carrierUniverseLevel, goalCarrierUniverseLevel});
        call = makeApplication(std::move(call), instantiatedCarrier);
        call = makeApplication(std::move(call), goalCarrier);
        call = makeApplication(std::move(call), std::move(motiveLambda));
        call = makeApplication(std::move(call), matchedSubterm);
        call = makeApplication(std::move(call), instantiatedRight);
        call = makeApplication(std::move(call),
                                std::move(instantiatedLemma));
        (void)current;
        (void)newCurrent;
        return call;
    }

ExpressionPointer Elaborator::desugarSimplify(
        const std::vector<SurfaceExpressionPointer>& lemmaSurfaces,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "simplify at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "simplify needs an expected type from context — use it "
                "in a calc step or as the body of a theorem with a "
                "declared equality conclusion");
        }
        EqualityComponents goal =
            extractEqualityComponents(expectedType, "simplify (goal)",
                                       line);

        // Prepare each lemma: elaborate to a kernel reference, close
        // its inferred type over localBinders (so references to outer
        // binders end up as BoundVariables — required for matching
        // against the closed-form goal), peel the Pi chain, then
        // extract the underlying Equality. Closing first ensures the
        // Pi binders end up at Bound(0..numBinders-1) (the matcher's
        // metavariable range) while localBinders refs land at higher
        // indices, where the matcher treats them as outer references.
        std::vector<SimplifyLemma> lemmas;
        lemmas.reserve(lemmaSurfaces.size());
        for (const auto& lemmaSurface : lemmaSurfaces) {
            SimplifyLemma prepared;
            prepared.lemmaReference =
                elaborateExpression(*lemmaSurface, localBinders);
            ExpressionPointer lemmaTypeOpened = weakHeadNormalForm(
                environment_,
                inferTypeInLocalContext(localBinders,
                                          prepared.lemmaReference));
            ExpressionPointer lemmaTypeClosed = closeOverLocalBinders(
                lemmaTypeOpened, localBinders, localBinders.size());
            int numBinders = 0;
            ExpressionPointer cursor = lemmaTypeClosed;
            while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                prepared.binderTypes.push_back(pi->domain);
                cursor = pi->codomain;
                ++numBinders;
            }
            prepared.numBinders = numBinders;
            EqualityComponents components =
                extractEqualityComponents(cursor, "simplify (lemma)",
                                           line);
            prepared.carrier = components.carrierType;
            prepared.leftPattern = components.leftEndpoint;
            prepared.rightPattern = components.rightEndpoint;
            prepared.carrierUniverseLevel =
                components.carrierUniverseLevel;
            lemmas.push_back(std::move(prepared));
        }

        // Iterate. At each step, look for any matching subterm; on
        // success, build the rewrite proof step and update the running
        // `current` value. Stop when `current` is definitionally equal
        // to the target, or when no lemma fires. `intermediates[i]` is
        // the running term BEFORE proofSteps[i]; intermediates.back()
        // is the final term after all steps.
        ExpressionPointer originalLeft = goal.leftEndpoint;
        ExpressionPointer current = goal.leftEndpoint;
        ExpressionPointer target = goal.rightEndpoint;
        std::vector<ExpressionPointer> proofSteps;
        std::vector<ExpressionPointer> intermediates;
        intermediates.push_back(current);
        const int iterationLimit = 200;

        // Build a context for definitional-equality checks, using the
        // localBinders (opened over fresh internal FreeVariables).
        auto checkDefinitionallyEqual =
            [&](ExpressionPointer left,
                ExpressionPointer right) -> bool {
            Context context = buildContextFromLocalBinders(localBinders);
            ExpressionPointer leftOpened = openOverLocalBinders(
                left, localBinders, localBinders.size());
            ExpressionPointer rightOpened = openOverLocalBinders(
                right, localBinders, localBinders.size());
            return isDefinitionallyEqual(environment_, context,
                                          leftOpened, rightOpened);
        };

        for (int iteration = 0; iteration < iterationLimit; ++iteration) {
            if (checkDefinitionallyEqual(current, target)) break;

            size_t matchedLemmaIndex = 0;
            std::vector<ExpressionPointer> bindings;
            ExpressionPointer matchedSubterm;
            if (!findFirstSimplifyMatch(current, lemmas,
                                          matchedLemmaIndex, bindings,
                                          matchedSubterm)) {
                throwElaborate(
                    "simplify: no lemma's left-hand side matches a "
                    "subterm of the current goal, and the goal is not "
                    "yet equal to its target — the rule set is "
                    "insufficient for this step");
            }
            const SimplifyLemma& matched = lemmas[matchedLemmaIndex];
            ExpressionPointer instantiatedRight = instantiatePattern(
                matched.rightPattern, bindings, matched.numBinders);
            // Replace the matched subterm with `instantiatedRight`. We
            // do this structurally — `abstractStructuralOccurrence`
            // would replace EVERY occurrence; we want the rewrite to
            // happen at the same set of positions that the proof step
            // covers (also "every occurrence"), so this is consistent.
            int occurrenceCount = 0;
            ExpressionPointer holed = abstractStructuralOccurrence(
                current, matchedSubterm, 0, occurrenceCount);
            ExpressionPointer newCurrent =
                substitute(holed, 0, instantiatedRight);
            ExpressionPointer step = buildSingleSimplifyStep(
                matched, bindings, current, matchedSubterm,
                newCurrent, goal.carrierType,
                goal.carrierUniverseLevel, instantiatedRight);
            proofSteps.push_back(std::move(step));
            current = std::move(newCurrent);
            intermediates.push_back(current);
        }

        if (!checkDefinitionallyEqual(current, target)) {
            throwElaborate(
                "simplify: hit iteration limit before reaching the "
                "target; the rule set may be non-confluent (e.g. "
                "naked commutativity)");
        }

        // Compose the proof. If no rewrites fired, the LHS was already
        // definitionally equal to the RHS — emit reflexivity at the
        // calc step's LHS (well-typed because expectedType is opaque
        // up to definitional equality).
        if (proofSteps.empty()) {
            ExpressionPointer reflexivityCall = makeConstant(
                "reflexivity",
                {goal.carrierUniverseLevel});
            reflexivityCall = makeApplication(
                std::move(reflexivityCall), goal.carrierType);
            reflexivityCall = makeApplication(
                std::move(reflexivityCall), goal.leftEndpoint);
            return reflexivityCall;
        }
        // Chain transitivities left-fold style. We tracked the
        // intermediate terms as we went, so we don't need to extract
        // them from the proof types (which would arrive in opened
        // form and require re-closing). The signature is
        //   Equality.transitivity.{u} (T : Type u) (x y z : T)
        //       (xEqY : Equality(T, x, y))
        //       (yEqZ : Equality(T, y, z))
        //   : Equality(T, x, z).
        ExpressionPointer composed = proofSteps[0];
        for (size_t i = 1; i < proofSteps.size(); ++i) {
            ExpressionPointer call = makeConstant(
                "Equality.transitivity",
                {goal.carrierUniverseLevel});
            call = makeApplication(std::move(call), goal.carrierType);
            call = makeApplication(std::move(call), originalLeft);
            call = makeApplication(std::move(call), intermediates[i]);
            call = makeApplication(std::move(call),
                                    intermediates[i + 1]);
            call = makeApplication(std::move(call), composed);
            call = makeApplication(std::move(call), proofSteps[i]);
            composed = std::move(call);
        }
        return composed;
    }


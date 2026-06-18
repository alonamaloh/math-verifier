// Out-of-line Elaborator method definitions: the rewrite and simplify tactics (desugarRewrite[Term], pattern instantiation, first-order match, simplify)
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::desugarRewriteTerm(
        SurfaceExpressionPointer equalityProofSurface,
        SurfaceExpressionPointer termSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "rewrite (term-level) at line " + std::to_string(line));
        TimedScope _scope(*this, "desugarRewriteTerm");
        ExpressionPointer equalityProofKernel = elaborateExpression(
            *equalityProofSurface, localBinders);
        ExpressionPointer equalityProofTypeOpened = weakHeadNormalForm(
            environment_,
            inferTypeInLocalContext(localBinders, equalityProofKernel));
        EqualityComponents lemmaComponentsOpened =
            extractEqualityComponents(
                equalityProofTypeOpened, "rewrite (equality proof)",
                line);
        ExpressionPointer carrierType = closeOverLocalBinders(
            lemmaComponentsOpened.carrierType,
            localBinders, localBinders.size());
        ExpressionPointer leftEndpoint = closeOverLocalBinders(
            lemmaComponentsOpened.leftEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer rightEndpoint = closeOverLocalBinders(
            lemmaComponentsOpened.rightEndpoint,
            localBinders, localBinders.size());

        ExpressionPointer termKernel = elaborateExpression(
            *termSurface, localBinders);
        // Deliberately DON'T weak-head-normalise term's inferred type
        // here: definitions like `Rational.LessThan(x, y) :=
        // And(LessOrEqual(x, y), Not(x = y))` unfold to a Constant
        // head whose argument appears twice (once on each conjunct),
        // and `Rational.IsNonneg(Quotient.class_of(rep))` unfolds via
        // `Quotient.lift` so the `Quotient.class_of` head disappears.
        // Either kills the structural-occurrence search. Keeping the
        // unreduced form gives us the user-visible motive shape, with
        // the rewrite endpoint exactly where they expect it. If no
        // match is found at this level we fall back to WHNF — that
        // covers sites where the term's type is genuinely behind a
        // definition that must be peeled.
        ExpressionPointer termTypeUnreduced =
            inferTypeInLocalContext(localBinders, termKernel);
        ExpressionPointer termTypeUnreducedClosed = closeOverLocalBinders(
            termTypeUnreduced, localBinders, localBinders.size());

        // Try six combinations of (term type, left endpoint) ×
        // (unreduced, head-beta/WHNF, deep-beta) in priority order.
        // WHNF-ing the left endpoint catches `congruenceOf(λr. P(r),
        // eq)` whose stated type's lhs is the unreduced beta-redex
        // `Application(λ, x)` while the term's inferred type carries
        // the beta-reduced `P(x)`. WHNF-ing the term type catches
        // definitions like `Rational.IsNonneg(...)` that wrap the
        // underlying claim. Deep-beta-reducing the term type catches
        // internal redexes (e.g. `sequenceFunction(λn. …, m)` from
        // Quotient.lift bodies in real analysis) that WHNF leaves
        // alone because it only reduces at the head.
        auto trySearch = [&](const ExpressionPointer& termTypeClosed,
                             const ExpressionPointer& lhs)
            -> std::pair<int, ExpressionPointer> {
            int count = 0;
            ExpressionPointer body = abstractStructuralOccurrence(
                termTypeClosed, lhs, /*currentDepth=*/0, count);
            return {count, std::move(body)};
        };

        // Beta-only reduction at the spine head. Required for
        // `congruenceOf(λr. P(r), eq)`: the equality's stated type
        // carries the unreduced beta-redex `(λr. P(r))(x)` as its
        // left endpoint, while the term's inferred type has the
        // beta-reduced `P(x)`. We can't use weakHeadNormalForm here
        // because that would δ-unfold any subsequent Constant head
        // (e.g. `Rational.padic_absolute_value`, which is defined as
        // a `Quotient.lift`) and lose the user-visible shape we want
        // to match against the term's type.
        auto betaReduceHead =
            [](ExpressionPointer e) -> ExpressionPointer {
            while (std::holds_alternative<Application>(e->node)) {
                std::vector<ExpressionPointer> args;
                ExpressionPointer head = e;
                while (auto* app = std::get_if<Application>(&head->node)) {
                    args.push_back(app->argument);
                    head = app->function;
                }
                std::reverse(args.begin(), args.end());
                if (auto* lambda = std::get_if<Lambda>(&head->node)) {
                    ExpressionPointer reduced =
                        substitute(lambda->body, 0, args[0]);
                    for (size_t i = 1; i < args.size(); ++i) {
                        reduced = makeApplication(reduced, args[i]);
                    }
                    e = reduced;
                } else {
                    break;
                }
            }
            return e;
        };

        ExpressionPointer leftEndpointBetaOpened =
            betaReduceHead(lemmaComponentsOpened.leftEndpoint);
        ExpressionPointer leftEndpointWhnf = closeOverLocalBinders(
            leftEndpointBetaOpened, localBinders, localBinders.size());

        // Try each (term form, endpoint form) combo in priority order
        // and remember each occurrence count for the failure
        // diagnostic. The body that wins is the FIRST combo that
        // returns exactly one occurrence — preferring the user's
        // surface shape (unreduced × unreduced) when possible — so a
        // success doesn't drift to a more-reduced form than needed.
        struct ComboAttempt {
            const char* label;
            int count = -1;  // -1 = not attempted
        };
        ComboAttempt attempts[6] = {
            {"unreduced term × unreduced endpoint"},
            {"unreduced term × β-reduced endpoint"},
            {"WHNF term × unreduced endpoint"},
            {"WHNF term × β-reduced endpoint"},
            {"deep-β term × unreduced endpoint"},
            {"deep-β term × β-reduced endpoint"},
        };
        int occurrenceCount = 0;
        ExpressionPointer abstractedBody;
        bool found = false;

        auto runAttempt =
            [&](int slot,
                const ExpressionPointer& termClosed,
                const ExpressionPointer& lhs) {
            if (found) return;
            auto [count, body] = trySearch(termClosed, lhs);
            attempts[slot].count = count;
            if (count == 1) {
                occurrenceCount = count;
                abstractedBody = std::move(body);
                found = true;
            }
        };

        runAttempt(0, termTypeUnreducedClosed, leftEndpoint);
        runAttempt(1, termTypeUnreducedClosed, leftEndpointWhnf);

        ExpressionPointer termTypeWhnfClosed;
        if (!found) {
            ExpressionPointer termTypeWhnf = weakHeadNormalForm(
                environment_, termTypeUnreduced);
            termTypeWhnfClosed = closeOverLocalBinders(
                termTypeWhnf, localBinders, localBinders.size());
            runAttempt(2, termTypeWhnfClosed, leftEndpoint);
            runAttempt(3, termTypeWhnfClosed, leftEndpointWhnf);
        }

        ExpressionPointer termTypeDeepBetaClosed;
        if (!found) {
            ExpressionPointer termTypeDeepBeta =
                deepBetaReduce(termTypeUnreduced);
            termTypeDeepBetaClosed = closeOverLocalBinders(
                termTypeDeepBeta, localBinders, localBinders.size());
            runAttempt(4, termTypeDeepBetaClosed, leftEndpoint);
            runAttempt(5, termTypeDeepBetaClosed, leftEndpointWhnf);
        }

        // Last resort: a definitional-equality-aware occurrence search.
        // The six structural combos compare each subterm STRUCTURALLY, so
        // they miss an endpoint present only up to definitional equality —
        // the canonical case being a structure projection on a concrete
        // bundle, `Ring.multiply(Polynomial.ring(r), x, y)`, against the
        // term's `Polynomial.multiply(r, x, y)`. This walker calls the
        // kernel's `isDefinitionallyEqual` (bounded; only at same-arity
        // applications) to dissolve that mismatch — the precise fix for
        // the bridging-`claim` tax (F1). Still requires EXACTLY ONE
        // occurrence, so an ambiguous match is rejected, not guessed.
        if (!found) {
            int defeqOccurrences = 0;
            int defeqBudget = 256;
            int targetArity = 0;
            ExpressionPointer head = leftEndpoint;
            while (auto* app = std::get_if<Application>(&head->node)) {
                ++targetArity;
                head = app->function;
            }
            ExpressionPointer body = abstractDefeqOccurrence(
                termTypeUnreducedClosed, leftEndpoint, targetArity,
                /*currentDepth=*/0, defeqOccurrences, defeqBudget);
            if (defeqOccurrences == 1) {
                occurrenceCount = 1;
                abstractedBody = std::move(body);
                found = true;
            }
        }

        // If no combo found exactly one occurrence, build a diagnostic
        // that breaks down each attempt's count so the user can tell
        // whether they have a 0-occurrence (mismatch), a >1-occurrence
        // (ambiguity), or both depending on normalisation level.
        auto buildFailureBreakdown = [&]() {
            std::string breakdown;
            for (const ComboAttempt& a : attempts) {
                if (a.count < 0) continue;
                breakdown += "\n      ";
                breakdown += a.label;
                breakdown += ": ";
                if (a.count == 0) {
                    breakdown += "0 occurrences";
                } else {
                    breakdown += std::to_string(a.count) +
                                 " occurrences";
                }
            }
            return breakdown;
        };

        // Use the unreduced form for the diagnostic display.
        ExpressionPointer termTypeOpened = termTypeUnreduced;

        // Multi-occurrence fallback: when the standard "exactly one"
        // search fails AND the caller provided an expected type, try
        // subset enumeration. For each (term form, endpoint form)
        // combo and each non-empty subset of the matching positions,
        // build the candidate motive and check whether motive(b) is
        // definitionally equal to the expected type. Use the first
        // match. Subsets are enumerated in "abstract all → singletons
        // → pairs+" order so the mathematically-natural choice (all
        // positions substituted) wins when applicable.
        if (!found && expectedType) {
            ExpressionPointer expectedTypeOpened = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            struct SearchCombo {
                ExpressionPointer termClosed;
                ExpressionPointer lhs;
            };
            std::vector<SearchCombo> combosBySlot;
            combosBySlot.push_back({termTypeUnreducedClosed, leftEndpoint});
            combosBySlot.push_back({termTypeUnreducedClosed, leftEndpointWhnf});
            if (termTypeWhnfClosed) {
                combosBySlot.push_back({termTypeWhnfClosed, leftEndpoint});
                combosBySlot.push_back({termTypeWhnfClosed, leftEndpointWhnf});
            } else {
                combosBySlot.push_back({});
                combosBySlot.push_back({});
            }
            if (termTypeDeepBetaClosed) {
                combosBySlot.push_back({termTypeDeepBetaClosed, leftEndpoint});
                combosBySlot.push_back({termTypeDeepBetaClosed, leftEndpointWhnf});
            } else {
                combosBySlot.push_back({});
                combosBySlot.push_back({});
            }
            for (int slot = 0; slot < 6 && !found; ++slot) {
                int count = attempts[slot].count;
                if (count < 2 || count > 16) continue;
                const SearchCombo& combo = combosBySlot[slot];
                if (!combo.termClosed) continue;
                uint32_t allMask = (1u << count) - 1;
                std::vector<uint32_t> subsetsToTry;
                subsetsToTry.push_back(allMask);
                for (int i = 0; i < count; ++i) {
                    if ((1u << i) != allMask) {
                        subsetsToTry.push_back(1u << i);
                    }
                }
                for (uint32_t s = 1; s < allMask; ++s) {
                    if (__builtin_popcount(s) >= 2) {
                        subsetsToTry.push_back(s);
                    }
                }
                for (uint32_t mask : subsetsToTry) {
                    int positionCounter = 0;
                    ExpressionPointer candidateBody =
                        abstractStructuralOccurrenceMasked(
                            combo.termClosed, combo.lhs,
                            /*currentDepth=*/0, positionCounter, mask);
                    // motive(b): substitute rightEndpoint for the new
                    // depth-0 binder in the abstracted body.
                    ExpressionPointer resultTypeClosed =
                        substitute(candidateBody, 0, rightEndpoint);
                    ExpressionPointer resultTypeOpened =
                        openOverLocalBinders(resultTypeClosed,
                            localBinders, localBinders.size());
                    if (isDefinitionallyEqual(environment_, openedContext,
                            resultTypeOpened, expectedTypeOpened)) {
                        abstractedBody = std::move(candidateBody);
                        occurrenceCount = count;
                        found = true;
                        break;
                    }
                }
            }
        }

        if (!found) {
            // Decide whether the dominant failure mode was "0 occurrences"
            // or "too many" so the headline matches what the user will
            // most likely act on.
            bool sawZeroOnly = true;
            int maxCount = 0;
            for (const ComboAttempt& a : attempts) {
                if (a.count <= 0) continue;
                sawZeroOnly = false;
                if (a.count > maxCount) maxCount = a.count;
            }
            std::string headline;
            if (sawZeroOnly) {
                headline =
                    "rewrite(eq, term): the equality's left endpoint "
                    "does not appear in term's type — neither "
                    "structurally nor up to definitional equality "
                    "(both were tried) — in (`"
                    + prettyPrintInLocalScope(termTypeOpened,
                                                localBinders)
                    + "`). Check the equation's direction (rewrite uses "
                      "its LEFT endpoint; wrap in Equality.symmetry to "
                      "flip), or restate the goal with `change <type>;` "
                      "to the spelling that exposes the endpoint.";
            } else {
                headline =
                    "rewrite(eq, term): the equality's left endpoint "
                    "appears "
                    + std::to_string(maxCount)
                    + " time(s) in term's type — `rewrite` needs "
                      "exactly one (or, when the expected type is "
                      "known, a subset whose substitution matches "
                      "the expected type). Use explicit "
                      "Equality.transport_proposition(...) to "
                      "disambiguate the position. (`"
                    + prettyPrintInLocalScope(termTypeOpened,
                                                localBinders)
                    + "`)";
            }
            throwElaborate(headline
                + "\n  Occurrence search:"
                + buildFailureBreakdown());
        }
        ExpressionPointer motiveLambda = makeLambda(
            "_rewriteHole", carrierType, std::move(abstractedBody));

        ExpressionPointer call = makeConstant(
            "Equality.transport_proposition",
            {lemmaComponentsOpened.carrierUniverseLevel});
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), std::move(motiveLambda));
        call = makeApplication(std::move(call), std::move(leftEndpoint));
        call = makeApplication(std::move(call), std::move(rightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(equalityProofKernel));
        call = makeApplication(std::move(call), std::move(termKernel));
        return call;
    }

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


// Out-of-line Elaborator method definitions: the core elaborateExpression dispatch + call-argument reordering
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

std::vector<SurfaceExpressionPointer> Elaborator::reorderArgumentsForCall(
        const std::vector<SurfaceArgument>& arguments,
        SurfaceExpressionPointer functionSurface,
        int line) {
        // Fast path: all positional. Just unwrap.
        bool anyNamed = false;
        for (const auto& a : arguments) {
            if (!a.name.empty()) { anyNamed = true; break; }
        }
        if (!anyNamed) {
            std::vector<SurfaceExpressionPointer> result;
            result.reserve(arguments.size());
            for (const auto& a : arguments) result.push_back(a.value);
            return result;
        }
        // Named-argument resolution. Look up the function's parameter
        // names by walking the kernel type's Pi chain.
        auto* headIdentifier = std::get_if<SurfaceIdentifier>(
            &functionSurface->node);
        if (!headIdentifier) {
            throwElaborate(
                "named arguments require a direct identifier as the "
                "function head (got a more complex expression at line "
                + std::to_string(line) + ")");
        }
        const Declaration* declaration =
            environment_.lookup(headIdentifier->qualifiedName);
        if (!declaration) {
            throwElaborate(
                "named arguments: function '"
                + headIdentifier->qualifiedName
                + "' is not in scope");
        }
        ExpressionPointer kernelType = declarationType(*declaration);
        std::vector<std::string> parameterNames;
        {
            ExpressionPointer cursor = kernelType;
            while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                parameterNames.push_back(pi->displayHint);
                cursor = pi->codomain;
            }
        }
        // Determine the "user-facing" parameter window. If the
        // function has registered implicit-argument count K, skip the
        // first K parameters. The remaining parameters' names are what
        // the user can reference.
        int implicitCount = environment_.implicitArgumentCount(
            headIdentifier->qualifiedName);
        if (implicitCount > static_cast<int>(parameterNames.size())) {
            implicitCount =
                static_cast<int>(parameterNames.size());
        }
        std::vector<std::string> userParamNames(
            parameterNames.begin() + implicitCount,
            parameterNames.end());
        size_t argCount = arguments.size();
        if (argCount > userParamNames.size()) {
            throwElaborate(
                "named arguments: function '"
                + headIdentifier->qualifiedName
                + "' has "
                + std::to_string(userParamNames.size())
                + " user-facing parameters but call supplies "
                + std::to_string(argCount));
        }
        // Two windows to try: the PREFIX [0..argCount) and the SUFFIX
        // [size-argCount..size). Prefix wins for fully-applied calls
        // and for explicit-parameter calls; suffix wins for desugared
        // calls (Quotient.sound, Quotient.mk, etc.) where the user
        // supplies only the trailing explicit parameters. Pick the
        // window that accepts every named argument; if both, prefix
        // wins as the more general default.
        std::vector<std::string> namesSupplied;
        for (const auto& a : arguments) {
            if (!a.name.empty()) namesSupplied.push_back(a.name);
        }
        auto windowAccepts =
            [&](size_t windowStart) -> bool {
                for (const auto& name : namesSupplied) {
                    bool found = false;
                    for (size_t i = 0; i < argCount; ++i) {
                        if (userParamNames[windowStart + i] == name) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) return false;
                }
                return true;
            };
        size_t windowStart = 0;
        bool prefixAccepts = windowAccepts(0);
        size_t suffixStart = userParamNames.size() - argCount;
        bool suffixAccepts =
            (suffixStart != 0) && windowAccepts(suffixStart);
        if (prefixAccepts) {
            windowStart = 0;
        } else if (suffixAccepts) {
            windowStart = suffixStart;
        } else {
            throwElaborate(
                "named arguments: no window of '"
                + headIdentifier->qualifiedName
                + "'s parameters matches the supplied names");
        }
        std::vector<SurfaceExpressionPointer> slots(
            argCount, SurfaceExpressionPointer{});
        std::vector<bool> slotFilled(argCount, false);
        // First pass: place named arguments.
        for (const auto& a : arguments) {
            if (a.name.empty()) continue;
            int paramIndex = -1;
            for (size_t i = 0; i < argCount; ++i) {
                if (userParamNames[windowStart + i] == a.name) {
                    paramIndex = static_cast<int>(i);
                    break;
                }
            }
            if (paramIndex < 0) {
                throwElaborate(
                    "named arguments: '"
                    + headIdentifier->qualifiedName
                    + "' has no parameter named '"
                    + a.name + "' in the resolved window");
            }
            if (slotFilled[paramIndex]) {
                throwElaborate(
                    "named arguments: parameter '"
                    + a.name + "' assigned twice");
            }
            slots[paramIndex] = a.value;
            slotFilled[paramIndex] = true;
        }
        // Second pass: positional arguments into the next unfilled
        // slot, in source order.
        size_t nextSlot = 0;
        for (const auto& a : arguments) {
            if (!a.name.empty()) continue;
            while (nextSlot < argCount && slotFilled[nextSlot]) {
                ++nextSlot;
            }
            if (nextSlot >= argCount) {
                throwElaborate(
                    "named arguments: too many positional arguments "
                    "after named-argument assignments");
            }
            slots[nextSlot] = a.value;
            slotFilled[nextSlot] = true;
            ++nextSlot;
        }
        return slots;
    }

ExpressionPointer Elaborator::elaborateExpression(
        const SurfaceExpression& expression,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType) {

        GoalScope goalScope(goalStack_, expectedType);

        // `goal` — refers to the elaborator's current expected type.
        // Resolves to the most-recent push on goalStack_. Note: a
        // bare `goal` here uses the OUTER expected type (the one
        // active when this elaborateExpression was called) rather
        // than the one just pushed for this call, because we want
        // the value of the surrounding goal, not the type of the
        // SurfaceGoal node itself.
        if (std::holds_alternative<SurfaceGoal>(expression.node)) {
            // Walk past the just-pushed frame (if any) to find the
            // surrounding goal.
            int top = static_cast<int>(goalStack_.size()) - 1;
            if (goalScope.pushed) top -= 1;
            if (top < 0) {
                throwElaborate(
                    "`goal` used where no expected type is "
                    "available — this position doesn't propagate "
                    "a goal from any enclosing context");
            }
            return goalStack_[top];
        }

        if (std::holds_alternative<SurfaceHole>(expression.node)) {
            // `?` outside a function-call argument position. The hole
            // can only be filled by goal-driven argument inference,
            // which fires at the application level; if we got here,
            // the user wrote `?` somewhere we don't (yet) try to
            // resolve it.
            throwElaborate(
                "`?` used outside a function-call argument position — "
                "no goal-driven inference applies here. Use `?` only "
                "for positional arguments of a known function (e.g. "
                "`Natural.successor_injective(?, ?, eq)`).");
        }

        if (auto* citeInferred =
                std::get_if<SurfaceCiteInferred>(&expression.node)) {
            // `<lemma>` with all explicit arguments inferred: expand to
            // `lemma(?, …, ?)` and let the hole-driven call path resolve them
            // (premises discharged from context, data args pinned thereby).
            auto* identifier = std::get_if<SurfaceIdentifier>(
                &citeInferred->function->node);
            if (!identifier) {
                throwElaborate(
                    "`by <lemma>` (in obtain) expects a lemma name");
            }
            const Declaration* decl =
                environment_.lookup(identifier->qualifiedName);
            if (!decl) {
                throwElaborate("unknown lemma '" + identifier->qualifiedName
                               + "' in `by`-citation");
            }
            ExpressionPointer declType = declarationType(*decl);
            int totalPi = declType ? countLeadingPis(declType) : 0;
            int implicitCount = environment_.implicitArgumentCount(
                identifier->qualifiedName);
            int explicitCount = totalPi - implicitCount;
            if (explicitCount <= 0) {
                throwElaborate("lemma '" + identifier->qualifiedName
                               + "' takes no explicit arguments to infer");
            }
            std::vector<SurfaceArgument> holeArgs;
            for (int i = 0; i < explicitCount; ++i) {
                holeArgs.push_back(
                    {"", makeSurfaceHole(expression.line, expression.column)});
            }
            SurfaceExpressionPointer call = makeSurfaceApplication(
                makeSurfaceIdentifier(
                    identifier->qualifiedName, identifier->universeArgs,
                    expression.line, expression.column),
                std::move(holeArgs), expression.line, expression.column);
            return elaborateExpression(*call, localBinders, expectedType);
        }

        if (auto* unfold =
                std::get_if<SurfaceUnfold>(&expression.node)) {
            // Flip each named definition's opacity from Opaque to
            // Transparent and DEFER the restore until the enclosing
            // theorem / definition finishes (so the kernel's final
            // typecheck inside `addDefinition` also sees the unfolded
            // view). Names that don't refer to definitions are a
            // user error; fail loudly.
            for (const std::string& name : unfold->names) {
                auto it = environment_.declarations.find(name);
                if (it == environment_.declarations.end()) {
                    throwElaborate(
                        "unfold: no declaration named `" + name + "`");
                }
                auto* def = std::get_if<Definition>(&it->second);
                if (!def) {
                    throwElaborate(
                        "unfold: `" + name + "` is not a definition "
                        "(unfolding only applies to definitions; "
                        "axioms / inductives have no body)");
                }
                pendingOpacityRestores_.push_back(
                    {name, def->opacity});
                def->opacity = Opacity::Transparent;
            }
            // Reduction depends on opacity, and the kernel's WHNF /
            // isDefEq caches don't track that — drop them so a stale
            // TRUE result computed under opaque opacity doesn't fool
            // the body's equality checks under the new transparent
            // view (or vice versa on the restore).
            invalidateKernelCaches();
            return elaborateExpression(
                *unfold->body, localBinders, expectedType);
        }

        if (auto* identifier =
                std::get_if<SurfaceIdentifier>(&expression.node)) {
            // Special case: bare `reflexivity` with an expected
            // equality type closes the step by inferring the
            // argument. Reads as "by reflexivity" in math.
            if (identifier->qualifiedName == "reflexivity"
                && identifier->universeArgs.empty()
                && expectedType) {
                ExpressionPointer expectedOpened = openOverLocalBinders(
                    expectedType, localBinders, localBinders.size());
                ExpressionPointer expectedWhnf = weakHeadNormalForm(
                    environment_, expectedOpened);
                EqualityComponents goalComps;
                try {
                    goalComps = extractEqualityComponents(
                        expectedWhnf, "bare reflexivity",
                        expression.line);
                } catch (const ElaborateError&) {
                    return elaborateIdentifier(
                        *identifier, localBinders,
                        expression.line, expression.column);
                }
                // Build reflexivity.{u}(carrier, leftEndpoint). The
                // kernel checks left and right are def-equal.
                ExpressionPointer call = makeConstant(
                    "reflexivity",
                    {goalComps.carrierUniverseLevel});
                ExpressionPointer carrier = closeOverLocalBinders(
                    goalComps.carrierType, localBinders,
                    localBinders.size());
                ExpressionPointer leftEndpoint = closeOverLocalBinders(
                    goalComps.leftEndpoint, localBinders,
                    localBinders.size());
                call = makeApplication(
                    std::move(call), std::move(carrier));
                call = makeApplication(
                    std::move(call), std::move(leftEndpoint));
                return call;
            }
            // Bare implicit-leading constant used where an expected type
            // is available — e.g. `IntegerMod.add` passed to `IsMonoid`'s
            // `operation` parameter (expected `C(m) → C(m) → C(m)`), or
            // `IntegerMod.zero` where `C(m)` is expected. The bare
            // constant's type is `Π{m}. …`, which does not match the
            // expected type because the leading implicit stays open.
            // Insert the implicit prefix as metavariables and solve them
            // by backward unification against the expected type, returning
            // the constant partially applied to the inferred implicits.
            //
            // Safe for the "bare lemma citation as a proof" case: if the
            // implicits cannot be recovered from the expected type the
            // inference throws and we fall through to the bare constant;
            // and if the open-implicit polymorphic form is what's wanted,
            // the expected type is itself a `Π{m}. …` whose head won't
            // unify with the opened result, so it falls through too.
            if (expectedType && identifier->universeArgs.empty()) {
                bool shadowedByLocal = false;
                for (const auto& binder : localBinders) {
                    if (binder.name == identifier->qualifiedName) {
                        shadowedByLocal = true;
                        break;
                    }
                }
                const Declaration* decl =
                    environment_.lookup(identifier->qualifiedName);
                if (!shadowedByLocal && decl
                    && currentDeclarationName_ != identifier->qualifiedName
                    && universeParameterCount(*decl) == 0
                    && environment_.implicitArgumentCount(
                           identifier->qualifiedName) > 0) {
                    int implicitCount =
                        environment_.implicitArgumentCount(
                            identifier->qualifiedName);
                    ExpressionPointer declType = declarationType(*decl);
                    if (declType) {
                        try {
                            CallInferenceResult inferred =
                                inferLeadingArguments(
                                    identifier->qualifiedName, declType,
                                    implicitCount, {}, localBinders,
                                    expectedType,
                                    "_identifierLeadingArgument_",
                                    expression.line);
                            ExpressionPointer head = makeConstant(
                                identifier->qualifiedName);
                            for (auto& leadingValue :
                                 inferred.leadingValues) {
                                head = makeApplication(
                                    std::move(head),
                                    std::move(leadingValue));
                            }
                            return head;
                        } catch (const ElaborateError&) {
                            // Could not infer the implicits from the
                            // expected type — fall through to the bare
                            // constant, preserving prior behavior.
                        }
                    }
                }
            }
            // `<lemma>` cited by NAME with no arguments where a concrete
            // (non-function) goal is expected: infer the lemma's arguments
            // by unifying its conclusion with the goal. Desugar to
            // `<lemma>(?, …, ?)` (one hole per explicit parameter) and run
            // the hole-driven call path, which solves the holes against the
            // expected type. Lets a user (or LLM) cite a fact by name
            // without remembering its argument order — e.g. `by add_zero`
            // instead of `by add_zero(a)`. Falls through to the bare
            // constant when the arguments can't be recovered from the goal,
            // so nullary citations and bare-value uses are unaffected.
            if (expectedType && identifier->universeArgs.empty()) {
                bool shadowedByLocal = false;
                for (const auto& binder : localBinders) {
                    if (binder.name == identifier->qualifiedName) {
                        shadowedByLocal = true;
                        break;
                    }
                }
                const Declaration* decl =
                    environment_.lookup(identifier->qualifiedName);
                if (!shadowedByLocal && decl
                    && currentDeclarationName_ != identifier->qualifiedName) {
                    ExpressionPointer declType = declarationType(*decl);
                    int totalPi = declType ? countLeadingPis(declType) : 0;
                    int implicitCount =
                        environment_.implicitArgumentCount(
                            identifier->qualifiedName);
                    int explicitCount = totalPi - implicitCount;
                    // Only when the lemma takes explicit args AND the goal
                    // is not itself a function type (a bare-value use of the
                    // lemma wants it unapplied — handled above / below).
                    bool expectedIsFunction = true;
                    try {
                        ExpressionPointer w = weakHeadNormalForm(
                            environment_,
                            openOverLocalBinders(expectedType, localBinders,
                                                  localBinders.size()));
                        expectedIsFunction =
                            std::holds_alternative<Pi>(w->node);
                    } catch (...) { expectedIsFunction = true; }
                    if (explicitCount > 0 && !expectedIsFunction) {
                        std::vector<SurfaceArgument> holeArgs;
                        for (int i = 0; i < explicitCount; ++i) {
                            holeArgs.push_back(
                                {"", makeSurfaceHole(expression.line,
                                                      expression.column)});
                        }
                        SurfaceExpressionPointer call =
                            makeSurfaceApplication(
                                makeSurfaceIdentifier(
                                    identifier->qualifiedName, {},
                                    expression.line, expression.column),
                                std::move(holeArgs),
                                expression.line, expression.column);
                        try {
                            ExpressionPointer holeCall = elaborateExpression(
                                *call, localBinders, expectedType);
                            // The hole solver can pin a metavariable from a
                            // PARTIAL structural match — e.g. unifying the
                            // lemma's conclusion `(-x)+x = 0` against a goal
                            // `p+0 = p+((-x)+x)` solves `x := 0` from the
                            // goal's left endpoint while silently ignoring the
                            // `(-x)` vs `p` mismatch, producing a fully-applied
                            // but WRONG proof. That wrong proof would then mask
                            // the congruence-step diff bridge (which wants the
                            // lemma left unapplied). Only accept the inferred
                            // call when its type actually proves the goal;
                            // otherwise fall through to the bare constant so
                            // the diff layer can match the lemma to a subterm.
                            ExpressionPointer holeCallType =
                                inferTypeInLocalContext(localBinders, holeCall);
                            ExpressionPointer goalOpened = openOverLocalBinders(
                                expectedType, localBinders,
                                localBinders.size());
                            Context goalContext =
                                buildContextFromLocalBinders(localBinders);
                            if (isDefinitionallyEqual(environment_, goalContext,
                                                       holeCallType,
                                                       goalOpened)) {
                                return holeCall;
                            }
                            // else: fall through to the bare constant
                        } catch (const ElaborateError&) {
                            // fall through to the bare constant
                        } catch (const TypeError&) {
                            // fall through to the bare constant
                        }
                    }
                }
            }
            return elaborateIdentifier(*identifier, localBinders,
                                        expression.line, expression.column);
        }
        if (auto* numeric =
                std::get_if<SurfaceNumericLiteral>(&expression.node)) {
            return elaborateNumericLiteral(*numeric, expression.line,
                                            expression.column);
        }
        if (auto* application =
                std::get_if<SurfaceApplication>(&expression.node)) {
            // A small family of identifier names is special-cased to
            // infer their typically-explicit arguments from the user-
            // supplied positional arguments.
            auto* headIdentifier = std::get_if<SurfaceIdentifier>(
                &application->function->node);
            // Reorder named arguments into positional order. If no
            // named arguments are present, the result is just the
            // positional values in their original order. After this
            // point, all downstream dispatch logic sees a uniform
            // positional argument list (`positionalArguments`).
            std::vector<SurfaceExpressionPointer> positionalArguments =
                reorderArgumentsForCall(
                    application->arguments,
                    application->function,
                    expression.line);
            // Hole detection: if any positional argument is `?`, the
            // user has opted into goal-driven inference at those slots.
            // Route to inferCallWithHoles with the function's
            // (universe-instantiated) type. The function must be a
            // known declaration with an identifier head — anonymous
            // function expressions and operator-dispatched calls fall
            // through to the regular path (which would error on `?`).
            bool anyHole = false;
            for (const auto& a : positionalArguments) {
                if (a && std::holds_alternative<SurfaceHole>(a->node)) {
                    anyHole = true; break;
                }
            }
            if (anyHole && headIdentifier
                && environment_.lookup(
                       headIdentifier->qualifiedName) != nullptr) {
                const std::string& name = headIdentifier->qualifiedName;
                const Declaration* decl =
                    environment_.lookup(name);
                ExpressionPointer declType = declarationType(*decl);
                // Universe-instantiate. Use user-provided
                // `.{u, v, …}` arguments if present; otherwise infer
                // universes from value args' types (concrete args
                // only — holes contribute nothing). Skip leading
                // implicit binders since the user supplies the
                // remaining args directly.
                int declaredImplicitCount =
                    environment_.implicitArgumentCount(name);
                int totalPiCount = countLeadingPis(declType);
                const std::vector<std::string>& universeParams =
                    declarationUniverseParameters(*decl);
                std::vector<LevelPointer> universeArgs;
                if (!headIdentifier->universeArgs.empty()) {
                    for (const auto& l :
                         headIdentifier->universeArgs) {
                        universeArgs.push_back(elaborateLevel(*l));
                    }
                } else if (!universeParams.empty()) {
                    std::vector<ExpressionPointer> probeArgs;
                    for (const auto& sa : positionalArguments) {
                        if (sa && std::holds_alternative<SurfaceHole>(
                                      sa->node)) {
                            probeArgs.push_back(nullptr);
                        } else {
                            try {
                                probeArgs.push_back(
                                    elaborateExpression(*sa,
                                        localBinders));
                            } catch (const ElaborateError&) {
                                probeArgs.push_back(nullptr);
                            }
                        }
                    }
                    universeArgs = inferUniverseArguments(
                        *decl, probeArgs, localBinders,
                        declaredImplicitCount);
                }
                ExpressionPointer instantiatedType = declType;
                if (!universeParams.empty()) {
                    instantiatedType = substituteUniverseLevels(
                        declType, universeParams, universeArgs);
                }
                // If the user supplied fewer args than the function
                // has Pis after stripping implicit-leading args, the
                // remaining leading-implicit args also need to be
                // inferred — extend the positional list with a `?`
                // prefix accordingly.
                std::vector<SurfaceExpressionPointer> fullArgs;
                int expectedArgCount =
                    totalPiCount - declaredImplicitCount;
                int implicitToFront = 0;
                if (static_cast<int>(positionalArguments.size())
                    == expectedArgCount
                    && declaredImplicitCount > 0) {
                    implicitToFront = declaredImplicitCount;
                }
                for (int i = 0; i < implicitToFront; ++i) {
                    fullArgs.push_back(makeSurfaceHole(
                        expression.line, expression.column));
                }
                for (const auto& a : positionalArguments) {
                    fullArgs.push_back(a);
                }
                std::vector<ExpressionPointer> resolvedArgs =
                    inferCallWithHoles(
                        name, instantiatedType,
                        fullArgs, localBinders,
                        expectedType, expression.line);
                ExpressionPointer call =
                    makeConstant(name, universeArgs);
                for (auto& v : resolvedArgs) {
                    call = makeApplication(std::move(call),
                                            std::move(v));
                }
                return call;
            }
            if (headIdentifier && headIdentifier->universeArgs.empty()) {
                const std::string& name = headIdentifier->qualifiedName;
                size_t argumentCount = positionalArguments.size();
                if (name == "congruenceOf" && argumentCount == 2) {
                    return desugarCongruenceOf(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "reflexivity" && argumentCount == 1) {
                    return desugarReflexivity(
                        positionalArguments[0],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "Equality.symmetry" && argumentCount == 1) {
                    return desugarEqualitySymmetry(
                        positionalArguments[0],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "Equality.transitivity"
                    && argumentCount == 2) {
                    return desugarEqualityTransitivity(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "rewrite" && argumentCount == 1) {
                    return desugarRewrite(
                        positionalArguments[0],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "rewrite" && argumentCount == 2) {
                    return desugarRewriteTerm(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders,
                        expectedType,
                        expression.line, expression.column);
                }
                if (name == "simplify" && argumentCount >= 1) {
                    return desugarSimplify(
                        positionalArguments,
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "absurd" && argumentCount == 1) {
                    return desugarAbsurd(
                        positionalArguments[0],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                // Quotient operations with implicit `T, R` inference.
                // Each user-facing form takes the explicit value args
                // only; the carrier and equivalence are recovered from
                // those args' types via a small custom desugar (the
                // standard implicit-argument machinery doesn't play
                // well with the combined universe-polymorphism +
                // implicit-binder case for axioms).
                if (name == "Quotient.mk" && argumentCount == 1) {
                    return desugarQuotientMk(
                        positionalArguments[0],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.sound" && argumentCount == 3) {
                    return desugarQuotientSound(
                        positionalArguments[0],
                        positionalArguments[1],
                        positionalArguments[2],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.lift" && argumentCount == 3) {
                    return desugarQuotientLift(
                        positionalArguments[0],
                        positionalArguments[1],
                        positionalArguments[2],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Exists.eliminate" && argumentCount == 2) {
                    return desugarExistsEliminate(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "And.eliminate" && argumentCount == 2) {
                    return desugarAndEliminate(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Or.eliminate" && argumentCount == 3) {
                    return desugarOrEliminate(
                        positionalArguments[0],
                        positionalArguments[1],
                        positionalArguments[2],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.induct"
                    && (argumentCount == 2 || argumentCount == 3)) {
                    // 2-arg form: motive inferred from expected type.
                    SurfaceExpressionPointer motiveArg =
                        argumentCount == 3 ? positionalArguments[0] : nullptr;
                    int atRepIndex = argumentCount == 3 ? 1 : 0;
                    int qIndex = argumentCount == 3 ? 2 : 1;
                    return desugarQuotientInduct(
                        motiveArg,
                        positionalArguments[atRepIndex],
                        positionalArguments[qIndex],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.induct_two"
                    && (argumentCount == 3 || argumentCount == 4)) {
                    SurfaceExpressionPointer motiveArg =
                        argumentCount == 4 ? positionalArguments[0] : nullptr;
                    int atRepIndex = argumentCount == 4 ? 1 : 0;
                    int q1Index = argumentCount == 4 ? 2 : 1;
                    int q2Index = argumentCount == 4 ? 3 : 2;
                    return desugarQuotientInductTwo(
                        motiveArg,
                        positionalArguments[atRepIndex],
                        positionalArguments[q1Index],
                        positionalArguments[q2Index],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.induct_three"
                    && (argumentCount == 4 || argumentCount == 5)) {
                    SurfaceExpressionPointer motiveArg =
                        argumentCount == 5 ? positionalArguments[0] : nullptr;
                    int atRepIndex = argumentCount == 5 ? 1 : 0;
                    int q1Index = argumentCount == 5 ? 2 : 1;
                    int q2Index = argumentCount == 5 ? 3 : 2;
                    int q3Index = argumentCount == 5 ? 4 : 3;
                    return desugarQuotientInductThree(
                        motiveArg,
                        positionalArguments[atRepIndex],
                        positionalArguments[q1Index],
                        positionalArguments[q2Index],
                        positionalArguments[q3Index],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                // Function-name overload resolution. When the head is
                // registered as an overload alias (via `overload alias
                // := F;`) and is not itself a regular declaration,
                // elaborate the arguments to infer their types, then
                // pick the unique candidate whose parameter-type
                // sequence matches.
                if (environment_.lookup(name) == nullptr) {
                    const std::vector<std::string>* candidates =
                        environment_.lookupOverloads(name);
                    if (candidates) {
                        return resolveOverloadedCall(
                            name, *candidates,
                            positionalArguments,
                            localBinders, expectedType,
                            expression.line, expression.column);
                    }
                }
                // Constructor parameter inference: if the head is a
                // constructor of a parameterised inductive and the user
                // supplied only the non-parameter arguments, infer the
                // parameter values from the value-argument types and
                // (when available) the expectedType.
                bool isCurrentDeclaration =
                    !currentDeclarationName_.empty()
                    && currentDeclarationName_ == name;
                const Declaration* environmentDeclaration =
                    environment_.lookup(name);
                if (!isCurrentDeclaration && environmentDeclaration) {
                    if (auto* constructor =
                            std::get_if<Constructor>(
                                environmentDeclaration)) {
                        const Declaration* inductiveLookup =
                            environment_.lookup(constructor->inductiveName);
                        const Inductive* inductive = inductiveLookup
                            ? std::get_if<Inductive>(inductiveLookup)
                            : nullptr;
                        if (inductive && inductive->numParameters > 0) {
                            int totalPiCount =
                                countLeadingPis(constructor->type);
                            int valueArgumentCount =
                                totalPiCount - inductive->numParameters;
                            if (static_cast<int>(argumentCount)
                                == valueArgumentCount) {
                                std::vector<LevelPointer> universeArguments =
                                    universeArgumentsForConstructorCall(
                                        *constructor, *inductive,
                                        expectedType);
                                return elaborateConstructorCallInferringParameters(
                                    *constructor, *inductive,
                                    positionalArguments,
                                    universeArguments, localBinders,
                                    expectedType, expression.line);
                            }
                        }
                    }
                }
                // Leading-argument inference for under-applied calls to
                // an Axiom or Definition (Theorem). When the user
                // supplies STRICTLY FEWER value arguments than the
                // declaration's total Pi count and an expectedType is
                // available, try to fill in the missing leading args
                // by backward-forward unification — the same machinery
                // constructor parameter inference uses.
                //
                // Engages only when:
                //   * argumentCount is between 1 and totalPiCount-1,
                //   * expectedType is non-null,
                //   * the declaration has no universe parameters OR
                //     the user supplied an explicit `.{...}` list of
                //     the right arity.
                // If inference cannot resolve every leading metavariable
                // we fall through to the partial-application path so the
                // user can still partially apply explicitly.
                // Engages with a non-null expectedType (backward +
                // forward inference) OR, when the declaration carries
                // leading `{x : T}` implicit binders, even WITHOUT an
                // expectedType — `inferLeadingArguments` resolves the
                // implicit prefix from the explicit args' types by
                // forward unification alone (e.g. `IntegerMod.add(x, y)`
                // recovering `{modulus}` from `x : IntegerMod(modulus)`).
                if (!isCurrentDeclaration
                    && environmentDeclaration
                    && argumentCount > 0
                    && (expectedType
                        || environment_.implicitArgumentCount(name) > 0)) {
                    ExpressionPointer declarationKernelType;
                    const std::vector<std::string>* declarationUniverseParams
                        = nullptr;
                    if (auto* axiom =
                            std::get_if<Axiom>(environmentDeclaration)) {
                        declarationKernelType = axiom->type;
                        declarationUniverseParams = &axiom->universeParameters;
                    } else if (auto* definition =
                                   std::get_if<Definition>(
                                       environmentDeclaration)) {
                        declarationKernelType = definition->type;
                        declarationUniverseParams =
                            &definition->universeParameters;
                    }
                    if (declarationKernelType) {
                        int totalPiCount =
                            countLeadingPis(declarationKernelType);
                        int declaredImplicitCount =
                            environment_.implicitArgumentCount(name);
                        // Two engagement modes:
                        //   (a) Declaration uses `{x : T}` implicit
                        //       binders. The user provides exactly the
                        //       explicit-arg count and we infer the
                        //       declared implicit prefix. (PAdic-style
                        //       convention prefixes also land here, since
                        //       `convention` adds implicit binders.)
                        //   (b) Declaration has no implicit binders and
                        //       is under-applied AGAINST A NON-FUNCTION
                        //       expected type. Some desugarings (e.g.
                        //       `by_induction … using <lemma>`) supply
                        //       trailing args and rely on the leading
                        //       ones being inferred — arity-based
                        //       inference fills them.
                        //
                        // Mode (b) is GATED on the expected type NOT being
                        // a function (Pi). An under-applied call whose
                        // expected type IS a function is a genuine PARTIAL
                        // APPLICATION (prefix supplied, trailing args
                        // missing); inferring "leading" args there would
                        // duplicate the first argument — e.g.
                        // `induced_map(G, H, f, homo)` passed where a
                        // function is expected used to become
                        // `induced_map G G H f homo …`. Those fall through
                        // to the partial-application path instead.
                        int numLeadingToInfer = 0;
                        if (declaredImplicitCount > 0) {
                            if (static_cast<int>(argumentCount)
                                == totalPiCount - declaredImplicitCount) {
                                numLeadingToInfer = declaredImplicitCount;
                            }
                        } else if (expectedType) {
                            ExpressionPointer expectedWhnf =
                                weakHeadNormalForm(environment_, expectedType);
                            bool expectedIsFunction =
                                std::holds_alternative<Pi>(expectedWhnf->node);
                            if (!expectedIsFunction) {
                                numLeadingToInfer =
                                    totalPiCount
                                    - static_cast<int>(argumentCount);
                            }
                        }
                        bool universesProvided =
                            declarationUniverseParams->empty()
                            || (headIdentifier->universeArgs.size()
                                == declarationUniverseParams->size());
                        bool explicitImplicitMode =
                            declaredImplicitCount > 0;
                        // Gate: in explicit-implicit mode we can infer
                        // universe args from value args (with skip), so
                        // we proceed even without `universesProvided`.
                        // In arity-based mode we keep the original gate
                        // to avoid changing behavior for under-applied
                        // polymorphic calls — Stage 2 handles those.
                        bool gateOk = explicitImplicitMode
                                      || universesProvided;
                        if (numLeadingToInfer > 0 && gateOk) {
                            // When the declaration uses explicit
                            // `{x : T}` binders, the user has
                            // committed to inference — any failure is
                            // a real error. When inference is engaged
                            // only via arity-based heuristics (the
                            // declaration has no implicit markers),
                            // we fall back to partial application so
                            // intentional under-application still
                            // works.
                            auto runInference = [&]() {
                                std::vector<LevelPointer> universeArguments;
                                if (!headIdentifier->universeArgs.empty()) {
                                    for (const auto& level :
                                         headIdentifier->universeArgs) {
                                        universeArguments.push_back(
                                            elaborateLevel(*level));
                                    }
                                } else if (!declarationUniverseParams
                                               ->empty()) {
                                    // No user-supplied `.{...}`, but the
                                    // declaration is universe-polymorphic.
                                    // Infer universes from the trailing
                                    // value args' types (skipping the
                                    // leading implicit binders the user
                                    // also didn't pass).
                                    std::vector<ExpressionPointer>
                                        valueArgsForUniverseInference;
                                    for (const auto& argumentSurface :
                                         positionalArguments) {
                                        try {
                                            valueArgsForUniverseInference
                                                .push_back(
                                                    elaborateExpression(
                                                        *argumentSurface,
                                                        localBinders));
                                        } catch (const ElaborateError&) {
                                            valueArgsForUniverseInference
                                                .push_back(nullptr);
                                        }
                                    }
                                    universeArguments =
                                        inferUniverseArguments(
                                            *environmentDeclaration,
                                            valueArgsForUniverseInference,
                                            localBinders,
                                            numLeadingToInfer);
                                }
                                ExpressionPointer instantiated =
                                    substituteUniverseLevels(
                                        declarationKernelType,
                                        *declarationUniverseParams,
                                        universeArguments);
                                CallInferenceResult inferred =
                                    inferLeadingArguments(
                                        name, instantiated,
                                        numLeadingToInfer,
                                        positionalArguments,
                                        localBinders, expectedType,
                                        "_callLeadingArgument_",
                                        expression.line);
                                ExpressionPointer head = makeConstant(
                                    name, universeArguments);
                                for (auto& leadingValue :
                                     inferred.leadingValues) {
                                    head = makeApplication(
                                        std::move(head),
                                        std::move(leadingValue));
                                }
                                for (auto& trailingValue :
                                     inferred.trailingValues) {
                                    head = makeApplication(
                                        std::move(head),
                                        std::move(trailingValue));
                                }
                                return head;
                            };
                            // Hard-error on inference failure only when
                            // the user committed to inference by both
                            // using explicit `{x : T}` binders AND giving
                            // an expectedType. When there is no
                            // expectedType (the relaxed entry above), a
                            // failure may simply mean the user passed the
                            // implicit arguments explicitly and
                            // positionally (e.g.
                            // `PAdicEquivalent(p, primality)` partially
                            // applying the convention-implicit prefix) —
                            // fall through to the generic application
                            // path, which binds args to Pis left-to-right
                            // including the implicit prefix.
                            if (explicitImplicitMode && expectedType) {
                                return runInference();
                            }
                            try {
                                return runInference();
                            } catch (const ElaborateError&) {
                                // Inference failed — fall through to
                                // partial / positional application.
                            }
                        }
                    }
                }
                // Stage 2 universe inference: if the head is a polymorphic
                // constant called without explicit `.{...}`, infer the
                // universe arguments by unifying the value arguments'
                // types against the declaration's parameter types.
                if (!isCurrentDeclaration
                    && environmentDeclaration
                    && universeParameterCount(*environmentDeclaration) > 0) {
                    std::vector<ExpressionPointer> valueArguments;
                    for (const auto& argumentSurface :
                         positionalArguments) {
                        valueArguments.push_back(elaborateExpression(
                            *argumentSurface, localBinders));
                    }
                    std::vector<LevelPointer> inferredUniverseArguments =
                        inferUniverseArguments(*environmentDeclaration,
                                                 valueArguments,
                                                 localBinders,
                                                 /*skipLeadingPis=*/0,
                                                 /*callSiteName=*/name,
                                                 /*errorOnUninferred=*/true);
                    ExpressionPointer head = makeConstant(
                        name, inferredUniverseArguments);
                    for (auto& valueArgument : valueArguments) {
                        head = makeApplication(std::move(head),
                                                std::move(valueArgument));
                    }
                    return head;
                }
            }
            ExpressionPointer head =
                elaborateExpression(*application->function, localBinders);
            // Propagate the expected argument type to each argument
            // elaboration by walking the head's type. Lets constructor
            // parameter inference inside lambda-shaped arguments see
            // the right expected type (e.g. for the handler functions
            // passed to Or.eliminate / Exists.eliminate).
            ExpressionPointer headType;
            try {
                headType = weakHeadNormalForm(environment_,
                    inferTypeInLocalContext(localBinders, head));
            } catch (...) {
                headType = nullptr;
            }
            for (const auto& argument : positionalArguments) {
                ExpressionPointer argumentExpectedType;
                if (headType) {
                    if (auto* pi =
                            std::get_if<Pi>(&headType->node)) {
                        argumentExpectedType = pi->domain;
                    }
                }
                ExpressionPointer argumentTerm =
                    elaborateExpression(*argument, localBinders,
                                         argumentExpectedType);
                // Diff-wrap and redundancy check on the argument too —
                // catches `f(congruenceOf(λ, P))` where bare `f(P)`
                // would work (e.g. `rewrite(congruenceOf(...), term)`
                // when the inner lemma alone has the equality shape
                // that diff inference can fit to `rewrite`'s expected
                // first-arg type).
                if (argumentExpectedType) {
                    argumentTerm = coerceToExpectedTypeViaDiff(
                        localBinders, argumentTerm,
                        argumentExpectedType);
                    checkRedundantCongruenceOfWrapper(
                        argument, localBinders, argumentExpectedType,
                        "function-call argument");
                }
                if (headType) {
                    if (auto* pi =
                            std::get_if<Pi>(&headType->node)) {
                        headType = weakHeadNormalForm(environment_,
                            substitute(pi->codomain, 0, argumentTerm));
                    } else {
                        headType = nullptr;
                    }
                }
                head = makeApplication(std::move(head),
                                        std::move(argumentTerm));
            }
            return head;
        }
        if (auto* piType = std::get_if<SurfacePiType>(&expression.node)) {
            return elaboratePiType(*piType, localBinders);
        }
        if (auto* lambda = std::get_if<SurfaceLambda>(&expression.node)) {
            return elaborateLambda(*lambda, localBinders, expectedType);
        }
        if (auto* let = std::get_if<SurfaceLet>(&expression.node)) {
            const char* claimSizeFlag2 =
                std::getenv("MATH_CLAIM_SIZES");
            bool dumpLetSize = claimSizeFlag2
                && claimSizeFlag2[0] != '\0'
                && claimSizeFlag2[0] != '0';
            auto tLet0 = std::chrono::steady_clock::now();
            ExpressionPointer letType;
            ExpressionPointer letValue;
            if (let->type) {
                letType = elaborateExpression(*let->type, localBinders);
                // Pass the declared type as the expected type for the
                // value so bidirectional elaborators (cases, anonymous
                // tuples, hammer, calc) can use it — without this,
                // `let h : T := ?;` can't trigger the hammer's
                // reflexivity-match etc.
                letValue = elaborateExpression(
                    *let->value, localBinders, letType);
            } else {
                // Untyped `let x := v;` — infer the type from the value.
                // Used by the `recalling` desugaring (which binds facts
                // whose types are not written) and any other type-free
                // local binding.
                letValue = elaborateExpression(*let->value, localBinders);
                // `recalling (<proposition>)`: a bare fact cited as a
                // proposition is auto-proved, so the discharge scope binds a
                // PROOF of it rather than the Sort-0 proposition itself.
                if (let->fromRecallingFact
                    && termIsProposition(localBinders, letValue)) {
                    letValue = proveCitedFact(
                        letValue, localBinders, expression.line);
                }
                letType = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, letValue),
                    localBinders, localBinders.size());
            }
            auto tLetType = std::chrono::steady_clock::now();
            auto tLetValue = std::chrono::steady_clock::now();
            // Diff-inference for non-calc equality coercion: covers
            // `claim X : succ(a) = succ(b) by eq` (desugars to a
            // SurfaceLet) without an explicit congruenceOf wrapper.
            if (let->type) {
                letValue = coerceToExpectedTypeViaDiff(
                    localBinders, letValue, letType);
            }
            auto tLetCoerce = std::chrono::steady_clock::now();
            checkRedundantCongruenceOfWrapper(
                let->value, localBinders, letType,
                "let value");
            if (dumpLetSize) {
                long long typeMs =
                    std::chrono::duration_cast<std::chrono::milliseconds>(
                        tLetType - tLet0).count();
                long long valueMs =
                    std::chrono::duration_cast<std::chrono::milliseconds>(
                        tLetValue - tLetType).count();
                long long coerceMs =
                    std::chrono::duration_cast<std::chrono::milliseconds>(
                        tLetCoerce - tLetValue).count();
                long long totalMs = typeMs + valueMs + coerceMs;
                if (totalMs >= 100) {
                    size_t typeSize = countExpressionNodes(letType);
                    std::cerr << "[let-size] " << moduleName_
                              << ":" << expression.line
                              << " name=" << let->name
                              << " typeSize=" << typeSize
                              << " typeMs=" << typeMs
                              << " valueMs=" << valueMs
                              << " coerceMs=" << coerceMs << "\n";
                }
            }
            std::vector<LocalBinder> extended = localBinders;
            // Capture the value on the LocalBinder so downstream
            // openedContext builders can mark it as let-bound (enabling
            // ζ-reduction in isDefinitionallyEqual on the FreeVariable),
            // and so the auto-prover's structural matchers can ζ-unfold
            // when matching on the closed term.
            extended.push_back({let->name, letType, letValue});
            // Propagate expectedType to body (shifted for new binder).
            ExpressionPointer bodyExpectedType =
                expectedType ? shift(expectedType, 1) : nullptr;
            ExpressionPointer letBody =
                elaborateExpression(*let->body, extended,
                                     bodyExpectedType);
            // Surface-text unused-name check on every named SurfaceLet
            // (covers `let X := V;`, legacy `claim X : T by V;`, and
            // `calc … as X;` desugaring). The kernel-level BV(0) check
            // is too lenient here: a downstream auto-prover call that
            // consumes the binding by type-match registers as BV(0)
            // referenced, even though the user never typed X — in
            // which case the anonymous form would behave identically
            // and the name is dead weight. Surface-text catches that.
            // Anonymous synthesised names (prefix `_`) are skipped by
            // warnIfSurfaceNameUnused itself.
            if (let->body) {
                if (let->fromCalcAsBinding) {
                    // Specialised message: the fix is to drop the
                    // `as NAME` postfix, not the calc itself.
                    if (reportUnusedNames_
                        && !let->name.empty()
                        && let->name[0] != '_'
                        && !surfaceMentionsName(
                            *let->body, let->name)) {
                        std::cerr << "warning: " << moduleName_
                            << ":" << expression.line
                            << ":" << expression.column
                            << ": `calc ... as " << let->name
                            << "` is never textually referenced —"
                               " drop the `as " << let->name
                            << "` to use the anonymous `calc ...;`"
                               " form (downstream calc steps still"
                               " find this equation by type-match)\n";
                    }
                } else if (reportUnusedNames_
                           && !let->name.empty()
                           && let->name[0] != '_'
                           && !surfaceMentionsName(
                               *let->body, let->name)) {
                    // The name is never typed in the body. Distinguish two
                    // cases by whether the binding's BV(0) appears anywhere
                    // in the elaborated body — if the auto-prover consumed
                    // the fact by type-match, its proof references BV(0):
                    //   • BV(0) absent  → the claim/let is genuinely DEAD
                    //     (used by neither name nor auto-prover); delete it.
                    //   • BV(0) present → only the NAME is dead; the fact is
                    //     load-bearing via type-match, so go anonymous (or
                    //     `note T;` if it's there for the reader).
                    bool bindingUsed =
                        referencesBoundVariable(letBody, 0);
                    if (!bindingUsed) {
                        std::cerr << "warning: " << moduleName_
                            << ":" << expression.line
                            << ":" << expression.column
                            << ": unused claim/let `" << let->name
                            << "` — its value is never used (not by name,"
                               " not by the auto-prover); delete the"
                               " binding, or turn it into `note <prop> [by"
                               " <proof>];` to keep it for the reader\n";
                    } else {
                        std::cerr << "warning: " << moduleName_
                            << ":" << expression.line
                            << ":" << expression.column
                            << ": unused name `" << let->name
                            << "` — the auto-prover consumes this fact by"
                               " type-match, so the name is dead weight:"
                               " switch to the anonymous form"
                               " (`claim T by V;`), or to `note T;` if it's"
                               " for the reader\n";
                    }
                }
            }
            return makeLet(let->name, std::move(letType),
                           std::move(letValue), std::move(letBody));
        }
        if (auto* ascription =
                std::get_if<SurfaceAscription>(&expression.node)) {
            // Pass the ascribed type as the expected type so bidirectional
            // elaborators (cases, anonymous tuples, hammer, calc) can
            // use it.
            ExpressionPointer ascribedType =
                elaborateExpression(*ascription->type, localBinders);
            // Carrier-identity shortcut: `(0 : T)` / `(1 : T)` where T
            // is a known constant with `T.zero` / `T.one` declared
            // emit the carrier's named identity directly. Without
            // this, the ascription would coerce a Natural literal into
            // T, producing a chain like
            // `Integer.to_rational(Natural.to_integer(zero))` — equal
            // to `T.zero` definitionally but opaque to `ring` (and to
            // any structural-search auto-prover) because the surface
            // shape is no longer the literal `T.zero`. Only fires when
            // the ascribed expression is a BARE numeric literal (not a
            // sub-expression like `1 + d`), so existing
            // `((1 + d) : Integer)` style ascriptions keep their
            // Natural-then-coerce semantics.
            if (auto* numeric = std::get_if<SurfaceNumericLiteral>(
                    &ascription->expression->node)) {
                int value = std::stoi(numeric->digits);
                if (value == 0 || value == 1) {
                    ExpressionPointer cursor = ascribedType;
                    while (auto* application =
                               std::get_if<Application>(&cursor->node)) {
                        cursor = application->function;
                    }
                    if (auto* head =
                            std::get_if<Constant>(&cursor->node)) {
                        std::string constantName = head->name
                            + (value == 0 ? ".zero" : ".one");
                        if (environment_.lookup(constantName)
                            != nullptr) {
                            return makeConstant(constantName);
                        }
                    }
                }
            }
            ExpressionPointer inner =
                elaborateExpression(*ascription->expression,
                                     localBinders, ascribedType);

            // Ascription doubles as a coercion: if `inner`'s inferred
            // type doesn't match the ascribed type but a registered
            // coercion chain bridges them, compose the chain and
            // apply it. The registry is populated by `coercion (S, T)
            // := F;` declarations and transitively closed at
            // registration time, so direct and multi-hop coercions
            // alike are a single lookup here.
            //
            // When no coercion fires, fall through to returning
            // `inner` directly; any type mismatch surfaces at the
            // eventual use site, exactly as it did before.
            if (!environment_.coercionRegistry.empty()) {
                try {
                    ExpressionPointer innerTypeOpened =
                        inferTypeInLocalContext(localBinders, inner);
                    ExpressionPointer ascribedTypeOpened =
                        openOverLocalBinders(ascribedType, localBinders,
                                              localBinders.size());
                    Context coercionContext =
                        buildContextFromLocalBinders(localBinders);
                    if (isDefinitionallyEqual(environment_, coercionContext,
                                                innerTypeOpened,
                                                ascribedTypeOpened)) {
                        return inner;
                    }
                    // Search registry for a chain from inner's head
                    // type to the ascribed head type. We match by raw
                    // head Constant name (without delta-reducing the
                    // type): the registry is keyed on the source-level
                    // type name, e.g. `Integer`, not the unfolded
                    // `Quotient(...)`.
                    auto headName =
                        [&](ExpressionPointer type) -> std::string {
                            ExpressionPointer cursor = type;
                            // Peel applications to find the head.
                            while (true) {
                                if (auto* app =
                                        std::get_if<Application>(
                                            &cursor->node)) {
                                    cursor = app->function;
                                    continue;
                                }
                                break;
                            }
                            if (auto* c =
                                    std::get_if<Constant>(&cursor->node)) {
                                return c->name;
                            }
                            return std::string{};
                        };
                    std::string innerHead = headName(innerTypeOpened);
                    std::string ascribedHead = headName(ascribedTypeOpened);
                    if (!innerHead.empty() && !ascribedHead.empty()) {
                        auto entry = environment_.coercionRegistry.find(
                            std::make_tuple(innerHead, ascribedHead));
                        if (entry != environment_.coercionRegistry.end()) {
                            ExpressionPointer call = std::move(inner);
                            for (const auto& funcName : entry->second) {
                                call = makeApplication(
                                    makeConstant(funcName),
                                    std::move(call));
                            }
                            return call;
                        }
                    }
                } catch (const TypeError&) {
                    // Inner expression's type couldn't be inferred —
                    // fall back to the no-coercion path.
                }
            }
            return inner;
        }
        if (auto* typeExpression =
                std::get_if<SurfaceType>(&expression.node)) {
            LevelPointer level = elaborateLevel(*typeExpression->level);
            return makeType(std::move(level));
        }
        if (std::get_if<SurfaceProposition>(&expression.node)) {
            return makeProposition();
        }
        if (auto* binary =
                std::get_if<SurfaceBinaryOperation>(&expression.node)) {
            if (binary->opSymbol == "=") {
                // Desugar `a = b` to `Equality.{u}(typeOfA, a, b)`.
                // The inferred type may contain Internal-origin FreeVars
                // introduced by our opening; close them back so the
                // resulting term is valid in the original context.
                ExpressionPointer leftKernel =
                    elaborateExpression(*binary->left, localBinders);
                ExpressionPointer leftTypeOpen =
                    inferTypeInLocalContext(localBinders, leftKernel);
                ExpressionPointer leftType = closeOverLocalBinders(
                    leftTypeOpen, localBinders, localBinders.size());
                // Pass leftType as expected type for the right side.
                // This lets `Quotient.mk(rep2)` (implicit T, R) back-
                // infer R from the carrier when the left side fixes it.
                ExpressionPointer rightKernel =
                    elaborateExpression(*binary->right, localBinders,
                                          leftType);
                LevelPointer universeLevel =
                    typeUniverseOf(localBinders, leftKernel);
                ExpressionPointer equalityReference =
                    makeConstant("Equality", {universeLevel});
                ExpressionPointer applied = makeApplication(
                    std::move(equalityReference), std::move(leftType));
                applied = makeApplication(std::move(applied),
                                           std::move(leftKernel));
                applied = makeApplication(std::move(applied),
                                           std::move(rightKernel));
                return applied;
            }
            // Negated relations: `a ≠ b` → `Not(a = b)`,
            // `a ≰ b` → `Not(a ≤ b)`, `a ∤ b` → `Not(a ∣ b)`. We
            // build the surface call to the positive relation and
            // recursively elaborate inside a `Not`.
            const std::string& sym = binary->opSymbol;
            const char* positive = nullptr;
            if (sym == "≠") positive = "=";
            else if (sym == "≰") positive = "≤";
            else if (sym == "∤") positive = "∣";
            if (positive) {
                if (environment_.lookup("Not") == nullptr) {
                    throw ElaborateError(
                        "operator '" + sym + "' requires `Not` in scope "
                        "(import Logic.basics) at line "
                        + std::to_string(expression.line));
                }
                SurfaceExpressionPointer positiveSurface =
                    makeSurfaceBinaryOperation(
                        positive, binary->left, binary->right,
                        expression.line, expression.column);
                ExpressionPointer positiveKernel =
                    elaborateExpression(*positiveSurface, localBinders);
                ExpressionPointer notCall = makeConstant("Not");
                return makeApplication(std::move(notCall),
                                        std::move(positiveKernel));
            }
            return desugarArithmeticOperator(
                binary->opSymbol, *binary->left, *binary->right,
                localBinders, expectedType, expression.line);
        }
        if (auto* unary =
                std::get_if<SurfaceUnaryOperation>(&expression.node)) {
            if (unary->opSymbol == "¬") {
                if (environment_.lookup("Not") == nullptr) {
                    throw ElaborateError(
                        "unary operator '¬' requires `Not` in scope "
                        "(import Logic.basics) at line "
                        + std::to_string(expression.line));
                }
                ExpressionPointer operandKernel =
                    elaborateExpression(*unary->operand, localBinders);
                ExpressionPointer call = makeConstant("Not");
                return makeApplication(std::move(call),
                                        std::move(operandKernel));
            }
            if (unary->opSymbol == "-") {
                // Dispatch unary `-` based on the operand's head type:
                // Integer.negate / Rational.negate / etc. If the raw
                // head type doesn't have a `.negate`, try operand-type
                // names from the binary `-` registry whose definition
                // δ-reduces to the operand's actual type — same fallback
                // as the binary operator dispatch.
                //
                // Propagate the outer expected type to the operand
                // when it has a Constant head — `-` is type-preserving
                // for numeric carriers, so short-form `Quotient.mk(rep)`
                // can fire under it.
                ExpressionPointer operandExpectedType = nullptr;
                if (expectedType
                    && std::holds_alternative<Constant>(
                            expectedType->node)) {
                    operandExpectedType = expectedType;
                }
                ExpressionPointer operandKernel =
                    elaborateExpression(*unary->operand, localBinders,
                                         operandExpectedType);
                ExpressionPointer operandType =
                    inferTypeInLocalContext(localBinders, operandKernel);
                std::string operandTypeName =
                    headConstantName(operandType);
                std::string negateFunction;
                if (!operandTypeName.empty()
                    && environment_.lookup(operandTypeName + ".negate")
                       != nullptr) {
                    negateFunction = operandTypeName + ".negate";
                }
                // Bundle carrier: an operand of type `X.carrier(...)`
                // negates via `X.negate` (the bundle's own negation),
                // not the nonexistent `X.carrier.negate`. Re-elaborate a
                // surface call `X.negate(operand)` so standard implicit-
                // argument inference fills the bundle instance — the same
                // trick the postfix `⁻¹` path uses for Group. This gives
                // `-a` to bundled structures (CommutativeRing, Ring).
                static const std::string carrierSuffix = ".carrier";
                if (negateFunction.empty()
                    && operandTypeName.size() > carrierSuffix.size()
                    && operandTypeName.compare(
                           operandTypeName.size() - carrierSuffix.size(),
                           carrierSuffix.size(), carrierSuffix) == 0) {
                    std::string bundleName = operandTypeName.substr(
                        0, operandTypeName.size() - carrierSuffix.size());
                    if (environment_.lookup(bundleName + ".negate")
                        != nullptr) {
                        SurfaceExpressionPointer call =
                            makeSurfaceApplication(
                                makeSurfaceIdentifier(
                                    bundleName + ".negate", {},
                                    expression.line, expression.column),
                                std::vector<SurfaceExpressionPointer>{
                                    unary->operand},
                                expression.line, expression.column);
                        return elaborateExpression(
                            *call, localBinders, expectedType);
                    }
                }
                if (negateFunction.empty()) {
                    // Fallback: search definitions whose body δ-reduces
                    // to the operand's WHNF. For each such T, check if
                    // `<T>.negate` exists; if so, dispatch there. Catches
                    // operands whose raw head is `Quotient(...)` but
                    // whose intended type alias (e.g. `Integer`) has a
                    // `.negate`.
                    ExpressionPointer operandWHNF = weakHeadNormalForm(
                        environment_, operandType);
                    for (const auto& [name, declaration]
                         : environment_.declarations) {
                        auto* def =
                            std::get_if<Definition>(&declaration);
                        if (!def) continue;
                        ExpressionPointer bodyWHNF = weakHeadNormalForm(
                            environment_, def->body);
                        if (structurallyEqual(bodyWHNF, operandWHNF)) {
                            if (environment_.lookup(name + ".negate")
                                != nullptr) {
                                negateFunction = name + ".negate";
                                break;
                            }
                        }
                    }
                }
                if (negateFunction.empty()) {
                    throw ElaborateError(
                        "unary operator '-' on type '"
                        + operandTypeName
                        + "': no `<T>.negate` in scope (line "
                        + std::to_string(expression.line) + ")");
                }
                // Re-elaborate as a plain call `negateFunction(operand)` so
                // standard implicit-argument inference fills any leading
                // implicits — e.g. `Polynomial.negate {r} : C(r) → C(r)` gets
                // `{r}` from the operand's type via canonical-bundle
                // resolution. Mirrors the postfix `⁻¹` path below.
                (void)operandKernel;
                SurfaceExpressionPointer negateCall = makeSurfaceApplication(
                    makeSurfaceIdentifier(negateFunction, {},
                        expression.line, expression.column),
                    std::vector<SurfaceExpressionPointer>{unary->operand},
                    expression.line, expression.column);
                return elaborateExpression(
                    *negateCall, localBinders, expectedType);
            }
            // Registered POSTFIX operators (e.g. `x⁻¹`). Dispatch on the
            // operand's type head against the operator registry's
            // postfix entries (right-type slot empty), then desugar to a
            // plain call `function(operand)` and re-elaborate it — that
            // reuses the standard implicit-argument inference, so a
            // dispatch function like `Group.inverse {g} : C(g) → C(g)`
            // gets its `{g}` filled from the operand's type.
            {
                ExpressionPointer operandKernel =
                    elaborateExpression(*unary->operand, localBinders);
                ExpressionPointer operandType =
                    inferTypeInLocalContext(localBinders, operandKernel);
                std::string operandTypeName = headConstantName(operandType);
                std::string postfixFunction = environment_.lookupOperator(
                    unary->opSymbol, operandTypeName, "");
                // δ-reduce fallback: a bundle-carrier / alias operand
                // (head e.g. `Quotient`) matches a registered operand
                // type whose definition body reduces to the same WHNF.
                if (postfixFunction.empty()) {
                    ExpressionPointer operandWHNF = weakHeadNormalForm(
                        environment_, operandType);
                    for (const auto& [key, funcName]
                         : environment_.operatorRegistry) {
                        const auto& [opSym, leftReg, rightReg] = key;
                        if (opSym != unary->opSymbol || !rightReg.empty()) {
                            continue;
                        }
                        const Declaration* leftDecl =
                            environment_.lookup(leftReg);
                        auto* leftDef = leftDecl
                            ? std::get_if<Definition>(leftDecl) : nullptr;
                        if (!leftDef) continue;
                        if (structurallyEqual(
                                weakHeadNormalForm(environment_, leftDef->body),
                                operandWHNF)) {
                            postfixFunction = funcName;
                            break;
                        }
                    }
                }
                if (!postfixFunction.empty()) {
                    SurfaceExpressionPointer call = makeSurfaceApplication(
                        makeSurfaceIdentifier(postfixFunction, {},
                            expression.line, expression.column),
                        std::vector<SurfaceExpressionPointer>{unary->operand},
                        expression.line, expression.column);
                    return elaborateExpression(*call, localBinders, expectedType);
                }
                throw ElaborateError(
                    "postfix operator '" + unary->opSymbol
                    + "' is not registered for operand type '"
                    + operandTypeName + "' (line "
                    + std::to_string(expression.line) + ")");
            }
        }
        if (auto* tuple =
                std::get_if<SurfaceAnonymousTuple>(&expression.node)) {
            return elaborateAnonymousTuple(*tuple, localBinders, expectedType,
                                            expression.line, expression.column);
        }
        if (auto* cases =
                std::get_if<SurfaceCases>(&expression.node)) {
            return elaborateCasesExpression(*cases, localBinders, expectedType,
                                             expression.line, expression.column);
        }
        if (std::get_if<SurfaceSorry>(&expression.node)) {
            return elaborateSorry(localBinders, expectedType,
                                   expression.line, expression.column);
        }
        if (auto* decide = std::get_if<SurfaceDecide>(&expression.node)) {
            return elaborateDecideExpression(
                *decide, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* note = std::get_if<SurfaceNote>(&expression.node)) {
            return elaborateNoteExpression(
                *note, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (std::get_if<SurfaceRing>(&expression.node)) {
            return elaborateRing(localBinders, expectedType,
                                  expression.line, expression.column);
        }
        if (auto* fieldTactic =
                std::get_if<SurfaceField>(&expression.node)) {
            return elaborateField(*fieldTactic, localBinders, expectedType,
                                   expression.line, expression.column);
        }
        if (auto* lincomb =
                std::get_if<SurfaceLinearCombination>(&expression.node)) {
            return elaborateLinearCombination(
                *lincomb, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* calc = std::get_if<SurfaceCalc>(&expression.node)) {
            return elaborateCalc(*calc, localBinders, expectedType,
                                  expression.line, expression.column);
        }
        if (auto* byInductionUsing =
                std::get_if<SurfaceByInductionUsing>(&expression.node)) {
            return elaborateByInductionUsing(
                *byInductionUsing, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* claim =
                std::get_if<SurfaceStructuredClaim>(&expression.node)) {
            return elaborateStructuredClaim(
                *claim, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* given =
                std::get_if<SurfaceGiven>(&expression.node)) {
            return elaborateGiven(
                *given, localBinders,
                expression.line, expression.column);
        }
        if (auto* choose =
                std::get_if<SurfaceChoose>(&expression.node)) {
            return elaborateChoose(
                *choose, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* strongInduction =
                std::get_if<SurfaceByStrongInduction>(&expression.node)) {
            return elaborateByStrongInduction(
                *strongInduction, localBinders, expectedType,
                expression.line, expression.column);
        }
        throw ElaborateError("unhandled surface expression variant");
    }


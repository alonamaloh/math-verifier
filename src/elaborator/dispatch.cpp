// Out-of-line Elaborator method definitions: the core elaborateExpression dispatch + call-argument reordering
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

// The built-in elaborator forms whose LEADING type/relation parameters
// are supplied by a custom desugar (below in this file) rather than by
// ordinary application — so named arguments address only the trailing
// window the desugar consumes (e.g. `Quotient.equivalent_implies_equal`'s
// `x, y, proof`, with `T, R` recovered from those args' types). For these,
// the windowed short-list reorder is correct. Every OTHER head is an
// ordinary lemma whose unsupplied parameters become inference holes.
static bool isDesugarShortFormHead(const std::string& name) {
    static const std::set<std::string> names = {
        "congruenceOf", "reflexivity", "Equality.symmetry",
        "Equality.transitivity", "rewrite", "simplify", "absurd",
        "Quotient.class_of", "Quotient.equivalent_implies_equal",
        "Quotient.lift", "Exists.eliminate", "And.eliminate",
        "Or.eliminate", "Quotient.induct", "Quotient.induct_two",
        "Quotient.induct_three",
    };
    return names.count(name) > 0;
}

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
        // Generic lemmas: a named or partial argument list pins specific
        // parameters by name and leaves the rest to goal-driven inference.
        // Build a FULL-ARITY list over the user-facing parameters — named
        // values at their parameter's slot, positional values in the
        // leading unfilled slots in order, and a `?` hole at every
        // unsupplied slot. A fully-applied call yields no holes and
        // elaborates as an ordinary application; a partial one routes to
        // the hole solver (`inferCallWithHoles`), which pins data
        // parameters from the goal and discharges premise parameters from
        // context. This is what makes `Lemma(x := e)` mean "apply Lemma
        // with parameter x set to e, everything else inferred" — and it
        // removes the old window-offset bug where a trailing named arg on
        // an ordinary lemma was silently applied to the WRONG (leading)
        // parameter.
        if (!isDesugarShortFormHead(headIdentifier->qualifiedName)) {
            std::vector<SurfaceExpressionPointer> full(
                userParamNames.size());
            for (const auto& a : arguments) {
                if (a.name.empty()) continue;
                int paramIndex = -1;
                for (size_t i = 0; i < userParamNames.size(); ++i) {
                    if (userParamNames[i] == a.name) {
                        paramIndex = static_cast<int>(i);
                        break;
                    }
                }
                if (paramIndex < 0) {
                    throwElaborate(
                        "named arguments: '"
                        + headIdentifier->qualifiedName
                        + "' has no parameter named '" + a.name + "'");
                }
                if (full[paramIndex]) {
                    throwElaborate(
                        "named arguments: parameter '"
                        + a.name + "' assigned twice");
                }
                full[paramIndex] = a.value;
            }
            size_t nextSlot = 0;
            for (const auto& a : arguments) {
                if (!a.name.empty()) continue;
                while (nextSlot < full.size() && full[nextSlot]) {
                    ++nextSlot;
                }
                if (nextSlot >= full.size()) {
                    throwElaborate(
                        "named arguments: too many positional arguments "
                        "after named-argument assignments");
                }
                full[nextSlot] = a.value;
                ++nextSlot;
            }
            for (auto& slot : full) {
                if (!slot) slot = makeSurfaceHole(line, 0);
            }
            return full;
        }
        // Desugar short-forms only, below.
        // Two windows to try: the PREFIX [0..argCount) and the SUFFIX
        // [size-argCount..size). Prefix wins for fully-applied calls
        // and for explicit-parameter calls; suffix wins for desugared
        // calls (Quotient.equivalent_implies_equal, Quotient.class_of, etc.) where the user
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

        // `--goal-at` recording: first-visit-wins per line keeps the
        // outermost node starting on a line (the enclosing statement);
        // a strictly-greater line not past the query refines toward
        // the queried position. Only PROPOSITION goals are recorded —
        // data-typed expected types (e.g. a calc-step endpoint's
        // `Natural`) would report `⊢ Natural`, which answers nothing;
        // skipping them makes the query fall back to the enclosing
        // statement's proof obligation. See goalAtSnapshot_'s docstring.
        if (goalAtLine_ >= 0 && expectedType
                && expression.line <= goalAtLine_
                && expression.line > goalAtSnapshot_.line
                && termIsProposition(localBinders, expectedType)) {
            goalAtSnapshot_ = {expression.line, expectedType, localBinders};
        }

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
            auto elaborateWithHoles =
                [&](int holeCount) -> ExpressionPointer {
                std::vector<SurfaceArgument> holeArgs;
                for (int i = 0; i < holeCount; ++i) {
                    holeArgs.push_back(
                        {"", makeSurfaceHole(expression.line,
                                             expression.column)});
                }
                SurfaceExpressionPointer call = makeSurfaceApplication(
                    makeSurfaceIdentifier(
                        identifier->qualifiedName, identifier->universeArgs,
                        expression.line, expression.column),
                    std::move(holeArgs), expression.line, expression.column);
                // No goal validates this citation's outcome (the obtained
                // existential just flows onward), so a silently-guessed
                // premise surfaces as a confusing failure far away — demand
                // an unambiguous discharge instead.
                requireUnambiguousDischarge_ = true;
                try {
                    ExpressionPointer cited = elaborateExpression(
                        *call, localBinders, expectedType);
                    requireUnambiguousDischarge_ = false;
                    return cited;
                } catch (...) {
                    requireUnambiguousDischarge_ = false;
                    throw;
                }
            };
            // The expected type here is the real destructure target (the
            // choose paths build it), so a citation that resolves at a
            // DIFFERENT type — e.g. the unapplied definition-spelled
            // conclusion when a premise pinned every stated hole — is
            // never useful; treat it like a failure for retry purposes.
            auto typeMatchesExpected =
                [&](ExpressionPointer term) -> bool {
                if (!expectedType) return true;
                try {
                    ExpressionPointer termType = inferTypeInLocalContext(
                        localBinders, term);
                    ExpressionPointer expectedOpened = openOverLocalBinders(
                        expectedType, localBinders, localBinders.size());
                    Context context =
                        buildContextFromLocalBinders(localBinders);
                    return isDefinitionallyEqual(
                        environment_, context, termType, expectedOpened);
                } catch (const TypeError&) {
                    return true;  // can't judge — keep the old behaviour
                } catch (const ElaborateError&) {
                    return true;
                }
            };
            // Retry with holes for the premises a definition-spelled
            // conclusion buries (`isCauchy : … → IsCauchy(f)` where
            // IsCauchy(f) = ∀ ε. 0 < ε → ∃ N. … — the ε and positivity
            // slots exist only after WHNF, so the syntactic count above
            // never opened them). The stated count stays primary:
            // `Not(P)` also δ-unfolds to a Pi, and an eager extra hole
            // would break every negation-concluding citation. On a
            // failed retry, the stated-form outcome stands — its
            // diagnostics match what the user wrote.
            int throughWhnf = declType
                ? countLeadingPisThroughWhnf(declType) : 0;
            int extendedCount = throughWhnf - implicitCount;
            try {
                ExpressionPointer stated =
                    elaborateWithHoles(explicitCount);
                if (extendedCount <= explicitCount
                    || typeMatchesExpected(stated)) {
                    return stated;
                }
                try {
                    ExpressionPointer extended =
                        elaborateWithHoles(extendedCount);
                    if (typeMatchesExpected(extended)) return extended;
                } catch (const ElaborateError&) {
                }
                return stated;
            } catch (const ElaborateError& statedError) {
                if (extendedCount <= explicitCount) throw;
                try {
                    return elaborateWithHoles(extendedCount);
                } catch (const ElaborateError&) {
                    throw statedError;
                }
            }
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
                            // Only adopt this implicit-only application when
                            // it ALREADY has the expected type. The whole
                            // point of this path is the bare operation case
                            // (`IntegerMod.add` where `C(m)→C(m)→C(m)` is
                            // expected): the implicit prefix `{m}` is the
                            // ONLY thing standing between the constant and a
                            // type-correct value. When EXPLICIT arguments
                            // still remain — e.g. a bundled-ring lemma
                            // `Ring.zero_multiply` (implicits
                            // carrier/add/…/ringProof, then an explicit
                            // `(x:carrier)`) cited where `multiply(zero,b) =
                            // zero` is expected — the implicit-only head is
                            // still a function type `(x:carrier) → …`, which
                            // does NOT prove the goal. Returning it here would
                            // shadow the by-name argument-inference path below,
                            // which fills the remaining explicit holes from the
                            // goal. So fall through unless the head is already
                            // a complete proof of the expected type.
                            ExpressionPointer headType =
                                inferTypeInLocalContext(localBinders, head);
                            ExpressionPointer expectedOpened =
                                openOverLocalBinders(
                                    expectedType, localBinders,
                                    localBinders.size());
                            Context headContext =
                                buildContextFromLocalBinders(localBinders);
                            if (isDefinitionallyEqual(
                                    environment_, headContext,
                                    headType, expectedOpened)) {
                                return head;
                            }
                            // else: explicit arguments remain — fall through.
                        } catch (const ElaborateError&) {
                            // Could not infer the implicits from the
                            // expected type — fall through to the bare
                            // constant, preserving prior behavior.
                        } catch (const TypeError&) {
                            // Type inference on the partial application
                            // failed — fall through as well.
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
            // A2 (statement-addressable facts), stage 1: a PROPOSITION
            // in function position addresses the in-scope fact with that
            // statement — `(∀ (k : Natural). P(k))(m)` applies the
            // universal hypothesis without naming it. Matched up to
            // defeq; two facts with the statement is a loud error (the
            // `given(...)` lookup provides both behaviours, so this is a
            // desugar onto it). Probed only for compound heads — a name
            // is already an address — and only when the head elaborates
            // as a Proposition value.
            if (!headIdentifier
                && !std::get_if<SurfaceLambda>(
                       &application->function->node)
                && !std::get_if<SurfaceGiven>(
                       &application->function->node)) {
                bool functionIsProposition = false;
                try {
                    ExpressionPointer probe = elaborateExpression(
                        *application->function, localBinders);
                    ExpressionPointer probeType = weakHeadNormalForm(
                        environment_,
                        openOverLocalBinders(
                            inferTypeInLocalContext(localBinders, probe),
                            localBinders, localBinders.size()));
                    auto* sort = std::get_if<Sort>(&probeType->node);
                    auto* level = sort
                        ? std::get_if<LevelConst>(&sort->level->node)
                        : nullptr;
                    functionIsProposition = level && level->value == 0;
                } catch (const ElaborateError&) {
                } catch (const TypeError&) {
                } catch (const AutoProverBudgetError&) {
                }
                if (functionIsProposition) {
                    SurfaceExpressionPointer addressed =
                        makeSurfaceApplication(
                            makeSurfaceGiven(application->function,
                                             expression.line,
                                             expression.column),
                            application->arguments,
                            expression.line, expression.column);
                    return elaborateExpression(*addressed, localBinders,
                                                expectedType);
                }
            }
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
            // Holes with a LOCAL-BINDER head — an induction hypothesis
            // or assumed lemma cited with `?` slots
            // (`no_smaller_solution(n, ?, k, ?, ?, ?)`). Same hole
            // solver; the head's type comes from the binder (lifted to
            // the closed scope), monomorphic, and the assembled call
            // applies the binder reference.
            if (anyHole && headIdentifier) {
                int N = static_cast<int>(localBinders.size());
                for (int b = N - 1; b >= 0; --b) {
                    if (localBinders[b].name
                            != headIdentifier->qualifiedName) {
                        continue;
                    }
                    ExpressionPointer binderType = liftBoundVariables(
                        localBinders[b].type, N - b, 0);
                    std::vector<ExpressionPointer> resolvedArgs =
                        inferCallWithHoles(
                            headIdentifier->qualifiedName, binderType,
                            positionalArguments, localBinders,
                            expectedType, expression.line);
                    ExpressionPointer call =
                        makeBoundVariable(N - 1 - b);
                    for (auto& v : resolvedArgs) {
                        call = makeApplication(std::move(call),
                                                std::move(v));
                    }
                    return call;
                }
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
                if (name == "rewrite") {
                    // RETIRED (A1 de-rewrite, owner call: `rewrite(…)` is
                    // CIC noise). The transport it performed is what the
                    // context-equality bridge does for a bare stated
                    // proposition; the internal desugarRewrite machinery
                    // survives as the citation-parity fallback (calc.cpp,
                    // inference.cpp) but has no surface spelling.
                    throwElaborate(
                        "the `rewrite(…)` form was retired: state the "
                        "equation (bare or `as NAME`), then state the "
                        "transported proposition itself — `P;` or "
                        "`P by <fact>;` — and the context-equality bridge "
                        "carries it across; on a chain step, cite the "
                        "equation directly (`by <equation>`)");
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
                if (name == "Quotient.class_of" && argumentCount == 1) {
                    return desugarQuotientMk(
                        positionalArguments[0],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.equivalent_implies_equal" && argumentCount == 3) {
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
                        //       binders. The user provides AT MOST the
                        //       explicit-arg count and we infer the
                        //       declared implicit prefix — a shorter
                        //       call is a genuine partial application
                        //       after the prefix (e.g.
                        //       `Subspace.inclusion(V, subset, subspace)`
                        //       leaving its function argument open), and
                        //       the prefix is still recovered from the
                        //       supplied args by forward unification. A
                        //       positional spelling that includes the
                        //       implicits has argumentCount == the full
                        //       Pi count, which this window excludes.
                        //       (PAdic-style convention prefixes also
                        //       land here, since `convention` adds
                        //       implicit binders.)
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
                        // function is expected would become
                        // `induced_map G G H f homo …`. Those fall through
                        // to the partial-application path instead.
                        int numLeadingToInfer = 0;
                        if (declaredImplicitCount > 0) {
                            if (static_cast<int>(argumentCount)
                                <= totalPiCount - declaredImplicitCount) {
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
                    // Probe-elaborate the arguments with no expected type, just
                    // to infer the universe levels. An argument that NEEDS an
                    // expected type to elaborate — an inline block-bodied
                    // lambda respect proof, say — fails the probe and comes
                    // back null; the universe levels don't depend on it (they
                    // come from the carrier/target type arguments), so this is
                    // harmless. Such arguments are re-elaborated below with the
                    // expected type the function's signature supplies.
                    std::vector<ExpressionPointer> valueArguments;
                    for (const auto& argumentSurface :
                         positionalArguments) {
                        try {
                            valueArguments.push_back(elaborateExpression(
                                *argumentSurface, localBinders));
                        } catch (const ElaborateError&) {
                            valueArguments.push_back(nullptr);
                        }
                    }
                    std::vector<LevelPointer> inferredUniverseArguments =
                        inferUniverseArguments(*environmentDeclaration,
                                                 valueArguments,
                                                 localBinders,
                                                 /*skipLeadingPis=*/0,
                                                 /*callSiteName=*/name,
                                                 /*errorOnUninferred=*/true);
                    // Walk the universe-instantiated signature so each argument
                    // sees its declared parameter type as its expected type —
                    // the same propagation the generic application path does —
                    // letting a lambda-shaped argument (whose body is a block)
                    // receive the respect-Pi codomain as its goal.
                    ExpressionPointer instantiatedType = substituteUniverseLevels(
                        declarationType(*environmentDeclaration),
                        declarationUniverseParameters(*environmentDeclaration),
                        inferredUniverseArguments);
                    ExpressionPointer head = makeConstant(
                        name, inferredUniverseArguments);
                    ExpressionPointer running = weakHeadNormalForm(
                        environment_, instantiatedType);
                    for (size_t i = 0; i < positionalArguments.size(); ++i) {
                        ExpressionPointer argumentExpectedType;
                        auto* pi = std::get_if<Pi>(&running->node);
                        if (pi) argumentExpectedType = pi->domain;
                        ExpressionPointer argumentTerm = valueArguments[i];
                        if (!argumentTerm) {
                            argumentTerm = elaborateExpression(
                                *positionalArguments[i], localBinders,
                                argumentExpectedType);
                        }
                        if (pi) {
                            running = weakHeadNormalForm(environment_,
                                substitute(pi->codomain, 0, argumentTerm));
                        }
                        head = makeApplication(std::move(head),
                                                std::move(argumentTerm));
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
            //
            // The walk stays in OPENED form (inferTypeInLocalContext
            // opens local binders into Internal FreeVariables), and each
            // peeled domain is CLOSED back over the local binders before
            // it is handed out — expected types are closed by convention.
            // Handing out the opened domain leaks Internal FreeVariables
            // into everything derived from it (a lambda argument's block
            // goal, and from there into proof terms the kernel rejects
            // as "unbound internal variable").
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
                        argumentExpectedType = closeOverLocalBinders(
                            pi->domain, localBinders,
                            localBinders.size());
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
                    // Also insert a user-declared registry coercion (the
                    // numeral/tower casts), so a bare `0` / `1 + 1` in an
                    // argument whose domain is `Real` lifts exactly as the
                    // `(0 : Real)` ascription would — no surprises, since it
                    // only fires when the types don't already agree.
                    argumentTerm = coerceToExpectedTypeViaRegistry(
                        localBinders, argumentTerm,
                        argumentExpectedType);
                    checkRedundantCongruenceOfWrapper(
                        argument, localBinders, argumentExpectedType,
                        "function-call argument");
                }
                if (headType) {
                    if (auto* pi =
                            std::get_if<Pi>(&headType->node)) {
                        // The argument is CLOSED; the walk is OPENED.
                        // Open the argument before substituting so the
                        // running type never mixes the two frames.
                        headType = weakHeadNormalForm(environment_,
                            substitute(pi->codomain, 0,
                                openOverLocalBinders(
                                    argumentTerm, localBinders,
                                    localBinders.size())));
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
            long long tLet0 = monotonicNanos();
            long long tLetTypeOnly = tLet0;
            ExpressionPointer letType;
            ExpressionPointer letValue;
            if (let->type) {
                letType = elaborateExpression(*let->type, localBinders);
                // `claim <proofTerm>;` desugars (parseStructuredClaimSequence)
                // to `let _anon : <proofTerm> := <claim> ;`, so the annotation
                // is itself a PROOF, not a type. Use the proof's type as the
                // binding's type — the mirror of the claim-proof coercion.
                // Fires only when the annotation is a proof of a proposition
                // (its type is a proposition), never for an ordinary type.
                {
                    Context letCtx =
                        buildContextFromLocalBinders(localBinders);
                    ExpressionPointer letTypeOpened = openOverLocalBinders(
                        letType, localBinders, localBinders.size());
                    if (!typeIsProposition(letCtx, letTypeOpened)) {
                        try {
                            ExpressionPointer annotationType = inferType(
                                environment_, letCtx, letTypeOpened);
                            if (typeIsProposition(letCtx, annotationType)) {
                                letType = closeOverLocalBinders(
                                    annotationType, localBinders,
                                    localBinders.size());
                            }
                        } catch (...) {
                            // not a proof — leave letType, the kernel will
                            // report the ordinary "not a type" error
                        }
                    }
                }
                tLetTypeOnly = monotonicNanos();
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
            long long tLetType = tLetTypeOnly;
            long long tLetValue = monotonicNanos();
            // Diff-inference for non-calc equality coercion: covers
            // `claim X : succ(a) = succ(b) by eq` (desugars to a
            // SurfaceLet) without an explicit congruenceOf wrapper.
            if (let->type) {
                letValue = coerceToExpectedTypeViaDiff(
                    localBinders, letValue, letType);
            }
            long long tLetCoerce = monotonicNanos();
            checkRedundantCongruenceOfWrapper(
                let->value, localBinders, letType,
                "let value");
            if (dumpLetSize) {
                long long typeMs = (tLetType - tLet0) / 1000000;
                long long valueMs = (tLetValue - tLetType) / 1000000;
                long long coerceMs = (tLetCoerce - tLetValue) / 1000000;
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
            // when matching on the closed term. Proof-valued lets (the
            // binder type is a Proposition: `claim X : T by V`,
            // `calc … as X`) are flagged so the kernel Context omits the
            // value — see LocalBinder::valueIsProof.
            bool valueIsProof = termIsProposition(localBinders, letType);
            extended.push_back({let->name, letType, letValue, valueIsProof});
            // Propagate expectedType to body (shifted for new binder).
            ExpressionPointer bodyExpectedType =
                expectedType ? shift(expectedType, 1) : nullptr;
            ExpressionPointer letBody =
                elaborateExpression(*let->body, extended,
                                     bodyExpectedType);
            // A4 lint: a forward `suppose … for contradiction { … }`
            // binds its conclusion (¬P, or P with the double negation
            // eliminated) anonymously for the rest of the block. If the
            // elaborated continuation never references that binding —
            // not even through an auto-prover step, which would leave a
            // BV reference — the whole reductio was a vestigial detour.
            if (reportUnusedNames_
                && let->name.rfind("_contradiction_fact_", 0) == 0
                && !referencesBoundVariable(letBody, 0)) {
                std::cerr << "warning: " << moduleName_
                          << ":" << expression.line
                          << ":" << expression.column
                          << ": the fact this `suppose … for "
                          "contradiction { … }` establishes is never "
                          "used afterward — a vestigial detour: delete "
                          "the block, or make its conclusion carry "
                          "weight in what follows\n";
            }
            // Surface-text unused-name check on every named SurfaceLet
            // (covers `let X := V;`, `claim X : T by V;`, and
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
                // Only 0/1 have named carrier constants; compare the
                // digit string directly (stoi would overflow on the
                // arbitrary-precision literals GMP numerals allow).
                if (numeric->digits == "0" || numeric->digits == "1") {
                    bool value = numeric->digits == "1";
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
                            return applyCoercionChain(std::move(inner),
                                                        entry->second);
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
        if (auto* foldBinder =
                std::get_if<SurfaceFoldBinder>(&expression.node)) {
            return elaborateFoldBinder(*foldBinder, localBinders,
                                        expectedType,
                                        expression.line, expression.column);
        }
        if (auto* ellipsisFold =
                std::get_if<SurfaceEllipsisFold>(&expression.node)) {
            return elaborateEllipsisFold(*ellipsisFold, localBinders,
                                          expectedType,
                                          expression.line,
                                          expression.column);
        }
        if (std::get_if<SurfaceSeriesFold>(&expression.node)) {
            throwElaborate(
                "an infinite series may only appear as one full side of "
                "an equality (`t1 + t2 + ... + g + ... = S` or "
                "`... = infinity`); series in term position and series "
                "inequalities are not supported in this version");
        }
        if (auto* binary =
                std::get_if<SurfaceBinaryOperation>(&expression.node)) {
            if (binary->opSymbol == "=") {
                // A series on one side: the whole relation is a
                // convergence proposition (A8 step 6).
                auto* leftSeries =
                    std::get_if<SurfaceSeriesFold>(&binary->left->node);
                auto* rightSeries =
                    std::get_if<SurfaceSeriesFold>(&binary->right->node);
                if (leftSeries && rightSeries) {
                    throwElaborate(
                        "a series may appear on only one side of the "
                        "relation");
                }
                if (leftSeries) {
                    return elaborateSeriesRelation(
                        *leftSeries, binary->right, localBinders,
                        expectedType, expression.line, expression.column);
                }
                if (rightSeries) {
                    return elaborateSeriesRelation(
                        *rightSeries, binary->left, localBinders,
                        expectedType, expression.line, expression.column);
                }
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
                // This lets `Quotient.class_of(rep2)` (implicit T, R) back-
                // infer R from the carrier when the left side fixes it.
                ExpressionPointer rightKernel =
                    elaborateExpression(*binary->right, localBinders,
                                          leftType);
                // Mixed-type equality (`(n : Natural) = (x : Real)`):
                // reconcile both sides to their join via the coercion
                // order, so the `Equality` runs at the common type rather
                // than forcing the right side into the left's type. See
                // PLAN_COERCIONS.md.
                {
                    ExpressionPointer rightTypeOpen =
                        inferTypeInLocalContext(localBinders, rightKernel);
                    ExpressionPointer rightType = closeOverLocalBinders(
                        rightTypeOpen, localBinders, localBinders.size());
                    std::string leftHead = headConstantName(leftType);
                    std::string rightHead = headConstantName(rightType);
                    if (leftHead != rightHead) {
                        if (auto combined = combineOperands(
                                leftHead, rightHead, leftType, rightType)) {
                            leftKernel = applyCoercionChain(
                                std::move(leftKernel), combined->coerceLeft);
                            if (!combined->coerceLeft.empty()) {
                                leftKernel = castPushToLeaves(
                                    leftKernel, localBinders).term;
                            }
                            rightKernel = applyCoercionChain(
                                std::move(rightKernel),
                                combined->coerceRight);
                            if (!combined->coerceRight.empty()) {
                                rightKernel = castPushToLeaves(
                                    rightKernel, localBinders).term;
                            }
                            leftType = combined->resultType;
                        }
                    }
                }
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
            // `a ≰ b` → `Not(a ≤ b)`, `a ∤ b` → `Not(a ∣ b)`,
            // `a ∉ b` → `Not(a ∈ b)`, `a ⊈ b` → `Not(a ⊆ b)`. We
            // build the surface call to the positive relation and
            // recursively elaborate inside a `Not`.
            const std::string& sym = binary->opSymbol;
            const char* positive = nullptr;
            if (sym == "≠") positive = "=";
            else if (sym == "≰") positive = "≤";
            else if (sym == "∤") positive = "∣";
            else if (sym == "∉") positive = "∈";
            else if (sym == "⊈") positive = "⊆";
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
                // A locally-bound `-` (an operator-named binder or
                // convention — e.g. an abstract additive group's negation):
                // apply it directly, before the type-directed `<T>.negate`
                // dispatch. Mirrors how a locally-bound binary `·`/`+`
                // resolves to its binder rather than a global operator.
                for (const auto& binder : localBinders) {
                    if (binder.name == "-") {
                        SurfaceExpressionPointer call = makeSurfaceApplication(
                            makeSurfaceIdentifier(
                                "-", {}, expression.line, expression.column),
                            std::vector<SurfaceExpressionPointer>{
                                unary->operand},
                            expression.line, expression.column);
                        return elaborateExpression(
                            *call, localBinders, expectedType);
                    }
                }
                // Dispatch unary `-` based on the operand's head type:
                // Integer.negate / Rational.negate / etc. If the raw
                // head type doesn't have a `.negate`, try operand-type
                // names from the binary `-` registry whose definition
                // δ-reduces to the operand's actual type — same fallback
                // as the binary operator dispatch.
                //
                // Propagate the outer expected type to the operand
                // when it has a Constant head — `-` is type-preserving
                // for numeric carriers, so short-form `Quotient.class_of(rep)`
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
                    // An operand whose type is (an alias of) an applied
                    // type former `F(args…)` with an `F.negate`: unfold
                    // bare alias heads step by step and check each head —
                    // `ComplexNumber` → `RingModulo(c, m)` dispatches to
                    // `RingModulo.negate` (implicits filled by the
                    // re-elaboration below).
                    ExpressionPointer aliasCursor = operandType;
                    for (int unfoldStep = 0;
                         unfoldStep < 8 && negateFunction.empty();
                         ++unfoldStep) {
                        ExpressionPointer aliasHead;
                        std::vector<ExpressionPointer> aliasArgs;
                        peelSpine(aliasCursor, aliasHead, aliasArgs);
                        auto* aliasConstant =
                            std::get_if<Constant>(&aliasHead->node);
                        if (!aliasConstant) break;
                        if (environment_.lookup(
                                aliasConstant->name + ".negate")
                            != nullptr) {
                            negateFunction =
                                aliasConstant->name + ".negate";
                            break;
                        }
                        if (!aliasArgs.empty()
                            || !aliasConstant->universeArguments.empty()) {
                            break;
                        }
                        const Declaration* aliasDeclaration =
                            environment_.lookup(aliasConstant->name);
                        if (!aliasDeclaration) break;
                        auto* aliasDefinition =
                            std::get_if<Definition>(aliasDeclaration);
                        if (!aliasDefinition
                            || aliasDefinition->opacity
                                   != Opacity::Transparent
                            || !aliasDefinition->universeParameters
                                    .empty()) {
                            break;
                        }
                        aliasCursor = aliasDefinition->body;
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
                // A locally-bound postfix operator (e.g. an abstract group's
                // `⁻¹`, bound as an operator convention/parameter): apply it
                // directly, before the type-directed registry dispatch.
                for (const auto& binder : localBinders) {
                    if (binder.name == unary->opSymbol) {
                        SurfaceExpressionPointer call = makeSurfaceApplication(
                            makeSurfaceIdentifier(
                                unary->opSymbol, {},
                                expression.line, expression.column),
                            std::vector<SurfaceExpressionPointer>{
                                unary->operand},
                            expression.line, expression.column);
                        return elaborateExpression(
                            *call, localBinders, expectedType);
                    }
                }
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
                    std::vector<SurfaceExpressionPointer> callArguments{
                        unary->operand};
                    // A dispatch function with IMPLICIT leading binders
                    // (`Field.reciprocal {f} (x, x≠0)`) must be
                    // saturated for the plain call path to insert the
                    // implicit prefix (it only fires when the explicit
                    // count matches) — pad the trailing side-condition
                    // slots with `?` holes, which discharge from scope
                    // exactly like the trailing-argument path below.
                    // Operators without implicits keep the partial-call
                    // route untouched.
                    int implicitCount = environment_.implicitArgumentCount(
                        postfixFunction);
                    if (implicitCount > 0) {
                        const Declaration* postfixDecl =
                            environment_.lookup(postfixFunction);
                        ExpressionPointer postfixType = postfixDecl
                            ? declarationType(*postfixDecl) : nullptr;
                        int explicitCount = postfixType
                            ? countLeadingPis(postfixType) - implicitCount
                            : 1;
                        for (int i = 1; i < explicitCount; ++i) {
                            callArguments.push_back(makeSurfaceHole(
                                expression.line, expression.column));
                        }
                    }
                    SurfaceExpressionPointer call = makeSurfaceApplication(
                        makeSurfaceIdentifier(postfixFunction, {},
                            expression.line, expression.column),
                        std::move(callArguments),
                        expression.line, expression.column);
                    // Elaborate the call then discharge any trailing
                    // propositional side-condition — a partial operator
                    // like `Real.reciprocal(x, x≠0)` behind `⁻¹` carries
                    // the proof as a trailing argument, exactly as
                    // `Real.divide` does behind `/`. (A total operator
                    // like `Group.inverse` has none, and a hole-saturated
                    // call arrives complete, so this is a no-op there.)
                    ExpressionPointer reciprocalCall =
                        elaborateExpression(*call, localBinders);
                    return dischargeTrailingSideConditions(
                        std::move(reciprocalCall), localBinders,
                        unary->opSymbol, expression.line);
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
        if (auto* groupTactic =
                std::get_if<SurfaceGroup>(&expression.node)) {
            return elaborateGroup(localBinders, expectedType,
                                  expression.line, expression.column,
                                  groupTactic->allowInverses);
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
        if (auto* eventuallyScope =
                std::get_if<SurfaceEventuallyScope>(&expression.node)) {
            return elaborateEventuallyScope(
                *eventuallyScope, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* blockTail =
                std::get_if<SurfaceBlockTail>(&expression.node)) {
            return elaborateBlockTail(
                *blockTail, localBinders, expectedType,
                expression.line, expression.column);
        }
        throw ElaborateError("unhandled surface expression variant");
    }

ExpressionPointer Elaborator::elaborateBlockTail(
        const SurfaceBlockTail& blockTail,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        // Data (or no expected type): the tail is a plain value — the
        // pre-A1 final-expression meaning, byte for byte.
        if (!expectedType || !termIsProposition(localBinders, expectedType)) {
            return elaborateExpression(
                *blockTail.expression, localBinders, expectedType);
        }
        // Proposition goal. Try the direct-proof reading first: `E`
        // elaborated AT the goal type is exactly the pre-A1 meaning and
        // keeps every proof that works today (proof terms, anonymous
        // tuples, coercion towers, implicit-argument resolution) working
        // unchanged. Speculative elaboration is state-safe (Frame /
        // GoalScope are RAII, cf. coerceToExpectedTypeViaDiff). Accept it
        // only when it actually PROVES the goal: a bare fact that is not the
        // goal (`a ≤ c` under goal `a ≤ c + 0`) elaborates to the
        // Proposition itself without throwing, so a plain success check
        // would wrongly bind the proposition as the block's value.
        // A `cases`/`by induction`-style tail is a PROOF construct — it can
        // never be read as a stated proposition, so the claim fallbacks
        // below would only mask its real error behind a misleading
        // "needs an expected type from context" (the statement reading
        // elaborates the tail as a TypedLet's type). Remember that, and
        // rethrow the direct reading's failure for such tails.
        bool tailIsProofOnly =
            std::holds_alternative<SurfaceCases>(blockTail.expression->node)
            || std::holds_alternative<SurfaceByInductionUsing>(
                   blockTail.expression->node)
            || std::holds_alternative<SurfaceByStrongInduction>(
                   blockTail.expression->node)
            // `witness E with proof` desugars to an anonymous tuple —
            // a proof term, never a stateable proposition; without this
            // the claim fallback masks the direct reading's real error
            // behind "anonymous tuple needs an expected type".
            || std::holds_alternative<SurfaceAnonymousTuple>(
                   blockTail.expression->node);
        try {
            ExpressionPointer direct = elaborateExpression(
                *blockTail.expression, localBinders, expectedType);
            if (bridgedResultProvesGoal(direct, expectedType, localBinders)) {
                return direct;
            }
            // A direct proof at a different spelling (a rep-level calc
            // under a class-equality goal): coerce it like the old arm
            // flow coerced its body — quotient-sound wrap, diff bridges.
            ExpressionPointer coercedDirect = coerceToExpectedTypeViaDiff(
                localBinders, direct, expectedType);
            if (coercedDirect
                && bridgedResultProvesGoal(coercedDirect, expectedType,
                                           localBinders)) {
                return coercedDirect;
            }
        } catch (const ElaborateError&) {
            if (tailIsProofOnly) throw;
        } catch (const TypeError&) {
            if (tailIsProofOnly) throw;
        } catch (const AutoProverBudgetError&) {
            // Speculative reading only — a budget blow here must fall
            // through to the statement route, never fail the build.
        }
        // A relation-chain tail (parseBodyExpressionOrStatement wraps body
        // chains in a BlockTail): the direct reading above already tried
        // the chain AT the goal — the final-calc direct path. The claim
        // fallbacks below don't apply to a calc node (it is a proof, not a
        // proposition); its statement reading is the anonymous
        // `{ <chain>; }` let + auto-close.
        if (std::holds_alternative<SurfaceCalc>(
                blockTail.expression->node)) {
            SurfaceExpressionPointer autoCloseCalc =
                makeSurfaceStructuredClaim(
                    makeSurfaceGoal(line, column), /*label=*/"",
                    /*byHint=*/nullptr, /*byCases=*/false, /*arms=*/{},
                    line, column);
            std::string calcName = "_calc_" + std::to_string(line)
                + "_" + std::to_string(column);
            SurfaceExpressionPointer chainDesugared = makeSurfaceLet(
                std::move(calcName), /*type=*/nullptr,
                blockTail.expression, std::move(autoCloseCalc),
                line, column);
            return elaborateExpression(
                *chainDesugared, localBinders, expectedType);
        }
        // Direct-coercion reading: prove the stated fact ONCE and coerce
        // its proof to the goal (quotient-sound wrap, diff bridges — the
        // route a final `calc`'s direct proof always took). Cheaper than
        // the statement fallback below, whose auto-close re-proves the
        // goal by context search — at a representative-level final fact
        // under a class-equality goal that search is an expensive-by-less
        // step, while this wrap is one defeq check.
        {
            ExpressionPointer factProof;
            try {
                SurfaceExpressionPointer statedFactOnly =
                    makeSurfaceStructuredClaim(
                        blockTail.expression, /*label=*/"",
                        /*byHint=*/nullptr, /*byCases=*/false,
                        /*arms=*/{}, line, column);
                factProof = elaborateExpression(
                    *statedFactOnly, localBinders, nullptr);
            } catch (const ElaborateError&) {
            } catch (const TypeError&) {
            } catch (const AutoProverBudgetError&) {
                // Speculative — fall through to the statement route.
            }
            if (factProof) {
                ExpressionPointer coerced = coerceToExpectedTypeViaDiff(
                    localBinders, factProof, expectedType);
                if (coerced
                    && bridgedResultProvesGoal(coerced, expectedType,
                                               localBinders)) {
                    return coerced;
                }
            }
        }
        // The direct reading failed: read `E` as the block's final
        // statement `E;` and let the implicit auto-close bridge its fact to
        // the goal — the keyword-free spelling of `claim E; done`. Mirrors
        // the parser's statement wrapper (a TypedLet whose type and value
        // are the stated fact) plus the auto-close `claim goal` it appends
        // for a statement-only block. The `_claim_anon_` prefix suppresses
        // the unused-name warning (the auto-close consumes the fact by
        // type-match, never by name).
        SurfaceExpressionPointer statedFact = makeSurfaceStructuredClaim(
            blockTail.expression, /*label=*/"", /*byHint=*/nullptr,
            /*byCases=*/false, /*arms=*/{}, line, column);
        SurfaceExpressionPointer autoClose = makeSurfaceStructuredClaim(
            makeSurfaceGoal(line, column), /*label=*/"", /*byHint=*/nullptr,
            /*byCases=*/false, /*arms=*/{}, line, column);
        std::string anonymousName = "_claim_anon_" + std::to_string(line)
            + "_" + std::to_string(column);
        SurfaceExpressionPointer desugared = makeSurfaceLet(
            std::move(anonymousName), /*type=*/blockTail.expression,
            /*value=*/std::move(statedFact), /*body=*/std::move(autoClose),
            line, column);
        return elaborateExpression(*desugared, localBinders, expectedType);
    }


ExpressionPointer Elaborator::elaborateFoldBinder(
        const SurfaceFoldBinder& fold,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this, "fold binder ("
            + (fold.operatorSymbol == "+" ? std::string("sum")
               : fold.operatorSymbol == "*" ? std::string("product")
               : "fold (" + fold.operatorSymbol + ")")
            + " " + fold.binderName + " from … to … of …)");
        // The carrier is the body's type: elaborate `λ(k : Natural). BODY`
        // bottom-up and read the Pi codomain. (The lambda is re-elaborated
        // inside the assembled call below; the duplicate pass is cheap and
        // keeps the assembly a plain surface application.)
        SurfaceExpressionPointer indexType =
            makeSurfaceIdentifier("Natural", {}, line, column);
        SurfaceBinder binder{{fold.binderName}, indexType, false};
        SurfaceExpressionPointer lambda =
            makeSurfaceLambda(binder, fold.body, line, column);
        ExpressionPointer lambdaKernel =
            elaborateExpression(*lambda, localBinders);
        ExpressionPointer lambdaType =
            inferTypeInLocalContext(localBinders, lambdaKernel);
        ExpressionPointer lambdaTypeWhnf =
            weakHeadNormalForm(environment_, lambdaType);
        auto* pi = std::get_if<Pi>(&lambdaTypeWhnf->node);
        if (!pi) {
            throwElaborate("fold binder: the body did not elaborate to a "
                           "function of the index (internal)");
        }
        if (referencesBoundVariable(pi->codomain, 0)) {
            throwElaborate(
                "fold binder: the body's type depends on the index variable "
                "`" + fold.binderName + "` — the fold needs one carrier "
                "type for every term");
        }
        std::string carrierName = headConstantName(pi->codomain);
        auto entry = environment_.foldOperationRegistry.find(
            std::make_tuple(fold.operatorSymbol, carrierName));
        if (entry == environment_.foldOperationRegistry.end()) {
            throwElaborate(
                "no `fold_operation (" + fold.operatorSymbol + ") on "
                + carrierName + "` is registered — the fold binder form "
                "needs the (operator, identity, monoid-laws) certificate; "
                "declare `fold_operation (" + fold.operatorSymbol + ") on "
                + carrierName + " := <IsMonoid witness>` (the numeric "
                "carriers register +/* in their instances files)");
        }
        if (!environment_.lookup("Algebra.Fold")) {
            throwElaborate(
                "the fold binder form elaborates to `Algebra.Fold` — "
                "import Algebra.aggregation");
        }
        // Count. Inclusive range LO..HI has count `(1 + HI) ∸ LO`,
        // monus-free when LO is a literal 0 or 1. An upper bound WRITTEN
        // `E - 1` is half-open notation for [LO, E): count `E ∸ LO` — so
        // `sum k from 0 to n - 1 of s(k)` is the empty sum at n = 0.
        auto isLiteral = [](const SurfaceExpressionPointer& e,
                            const char* digits) {
            auto* numeral = std::get_if<SurfaceNumericLiteral>(&e->node);
            return numeral && numeral->digits == digits;
        };
        SurfaceExpressionPointer halfOpenBound;
        if (auto* upperOp =
                std::get_if<SurfaceBinaryOperation>(&fold.upperBound->node)) {
            if (upperOp->opSymbol == "-" && isLiteral(upperOp->right, "1")) {
                halfOpenBound = upperOp->left;
            }
        }
        SurfaceExpressionPointer count;
        if (halfOpenBound) {
            if (isLiteral(fold.lowerBound, "0")) {
                count = halfOpenBound;
            } else {
                count = makeSurfaceApplication(
                    makeSurfaceIdentifier("Natural.monus", {}, line, column),
                    std::vector<SurfaceExpressionPointer>{
                        halfOpenBound, fold.lowerBound},
                    line, column);
            }
        } else if (isLiteral(fold.lowerBound, "0")) {
            count = makeSurfaceBinaryOperation(
                "+", makeSurfaceNumericLiteral("1", line, column),
                fold.upperBound, line, column);
        } else if (isLiteral(fold.lowerBound, "1")) {
            count = fold.upperBound;
        } else {
            count = makeSurfaceApplication(
                makeSurfaceIdentifier("Natural.monus", {}, line, column),
                std::vector<SurfaceExpressionPointer>{
                    makeSurfaceBinaryOperation(
                        "+", makeSurfaceNumericLiteral("1", line, column),
                        fold.upperBound, line, column),
                    fold.lowerBound},
                line, column);
        }
        // Carrier, operation and identity come from the WITNESS TYPE as
        // core expressions (closed and global). The registry's stored
        // names are head constants only — enough for lookup, but a
        // composite identity (Natural's `1` = successor(zero)) has no
        // one-name spelling, so the term is assembled in core directly.
        const Declaration* witness =
            environment_.lookup(entry->second.witnessName);
        if (!witness) {
            throwElaborate("fold binder: the registered IsMonoid witness '"
                           + entry->second.witnessName
                           + "' is not in scope (internal)");
        }
        ExpressionPointer witnessType = declarationType(*witness);
        std::vector<ExpressionPointer> reversedArguments;
        ExpressionPointer cursor = witnessType;
        while (auto* application = std::get_if<Application>(&cursor->node)) {
            reversedArguments.push_back(application->argument);
            cursor = application->function;
        }
        if (reversedArguments.size() != 3) {
            throwElaborate("fold binder: the registered witness '"
                           + entry->second.witnessName
                           + "' does not have an IsMonoid(carrier, "
                           "operation, identity) type (internal)");
        }
        ExpressionPointer carrierCore = reversedArguments[2];
        ExpressionPointer operationCore = reversedArguments[1];
        ExpressionPointer identityCore = reversedArguments[0];
        ExpressionPointer naturalType = makeConstant("Natural");
        ExpressionPointer lowerKernel = elaborateExpression(
            *fold.lowerBound, localBinders, naturalType);
        ExpressionPointer countKernel = elaborateExpression(
            *count, localBinders, naturalType);
        // `Algebra.Fold(A, op, identity, λk. BODY, LO, count)`, assembled
        // in core: every piece is either global (carrier/op/identity) or
        // an elaborateExpression result over the same localBinders, so
        // the closed-over-binders representation is uniform.
        ExpressionPointer term = makeApplication(makeApplication(
            makeApplication(makeApplication(makeApplication(makeApplication(
                makeConstant("Algebra.Fold"), carrierCore), operationCore),
                identityCore), lambdaKernel), lowerKernel), countKernel);
        if (expectedType) {
            // The binder form produces a carrier element; v1 does not
            // coerce it. If the context wants a different type, write the
            // cast (or `Algebra.Fold`) explicitly.
            bool matches = false;
            try {
                ExpressionPointer termType =
                    inferTypeInLocalContext(localBinders, term);
                Context context = buildContextFromLocalBinders(localBinders);
                matches = isDefinitionallyEqual(
                    environment_, context, termType, expectedType);
            } catch (...) { matches = false; }
            if (!matches) {
                throwElaborate(
                    "the fold binder form has carrier type `"
                    + prettyPrint(carrierCore) + "`, which is not the "
                    "expected type here — write the cast explicitly");
            }
        }
        return term;
    }

// ----------------------------------------------------------------------
// Ellipsis fold recognition (A8 step 4). File-local surface helpers.

namespace {

// Ground evaluation of a CLOSED elaborated Natural term over the known
// arithmetic heads. Recognition-side only: it establishes truth for the
// prefix verification and the 0/1 probe; no proof term is built (the
// notation is a compile-time shape check, not a proof obligation).
std::optional<unsigned long long> evaluateGroundNatural(
        const ExpressionPointer& expression) {
    if (auto* constant = std::get_if<Constant>(&expression->node)) {
        // Natural's constructors are the BARE `zero` / `successor`.
        if (constant->name == "zero") return 0ull;
        return std::nullopt;
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        // Peel the spine.
        std::vector<ExpressionPointer> args;
        ExpressionPointer head = expression;
        while (auto* app = std::get_if<Application>(&head->node)) {
            args.push_back(app->argument);
            head = app->function;
        }
        std::reverse(args.begin(), args.end());
        auto* constant = std::get_if<Constant>(&head->node);
        if (!constant) return std::nullopt;
        auto unary = [&](auto f) -> std::optional<unsigned long long> {
            if (args.size() != 1) return std::nullopt;
            auto a = evaluateGroundNatural(args[0]);
            if (!a) return std::nullopt;
            return f(*a);
        };
        auto binary = [&](auto f) -> std::optional<unsigned long long> {
            if (args.size() != 2) return std::nullopt;
            auto a = evaluateGroundNatural(args[0]);
            auto b = evaluateGroundNatural(args[1]);
            if (!a || !b) return std::nullopt;
            return f(*a, *b);
        };
        if (constant->name == "successor") {
            return unary([](unsigned long long a) { return a + 1; });
        }
        if (constant->name == "Natural.add") {
            return binary([](unsigned long long a, unsigned long long b) {
                return a + b; });
        }
        if (constant->name == "Natural.multiply") {
            return binary([](unsigned long long a, unsigned long long b) {
                return a * b; });
        }
        if (constant->name == "Natural.monus") {
            return binary([](unsigned long long a, unsigned long long b) {
                return a >= b ? a - b : 0; });
        }
        (void)application;
        return std::nullopt;
    }
    return std::nullopt;
}

bool surfaceStructurallyEqual(const SurfaceExpressionPointer& a,
                              const SurfaceExpressionPointer& b);

bool surfaceArgumentsEqual(const std::vector<SurfaceArgument>& a,
                           const std::vector<SurfaceArgument>& b) {
    if (a.size() != b.size()) return false;
    for (size_t i = 0; i < a.size(); ++i) {
        if (a[i].name != b[i].name) return false;
        if (!surfaceStructurallyEqual(a[i].value, b[i].value)) return false;
    }
    return true;
}

// Structural surface equality over the expression subset the ellipsis
// notation can contain. Unknown node kinds compare unequal (conservative:
// recognition then falls through to the probe or errors out).
bool surfaceStructurallyEqual(const SurfaceExpressionPointer& a,
                              const SurfaceExpressionPointer& b) {
    if (auto* ia = std::get_if<SurfaceIdentifier>(&a->node)) {
        auto* ib = std::get_if<SurfaceIdentifier>(&b->node);
        return ib && ia->qualifiedName == ib->qualifiedName;
    }
    if (auto* na = std::get_if<SurfaceNumericLiteral>(&a->node)) {
        auto* nb = std::get_if<SurfaceNumericLiteral>(&b->node);
        return nb && na->digits == nb->digits;
    }
    if (auto* pa = std::get_if<SurfaceApplication>(&a->node)) {
        auto* pb = std::get_if<SurfaceApplication>(&b->node);
        return pb
            && surfaceStructurallyEqual(pa->function, pb->function)
            && surfaceArgumentsEqual(pa->arguments, pb->arguments);
    }
    if (auto* oa = std::get_if<SurfaceBinaryOperation>(&a->node)) {
        auto* ob = std::get_if<SurfaceBinaryOperation>(&b->node);
        return ob && oa->opSymbol == ob->opSymbol
            && surfaceStructurallyEqual(oa->left, ob->left)
            && surfaceStructurallyEqual(oa->right, ob->right);
    }
    if (auto* ua = std::get_if<SurfaceUnaryOperation>(&a->node)) {
        auto* ub = std::get_if<SurfaceUnaryOperation>(&b->node);
        return ub && ua->opSymbol == ub->opSymbol
            && surfaceStructurallyEqual(ua->operand, ub->operand);
    }
    if (auto* ca = std::get_if<SurfaceAscription>(&a->node)) {
        auto* cb = std::get_if<SurfaceAscription>(&b->node);
        return cb
            && surfaceStructurallyEqual(ca->expression, cb->expression)
            && surfaceStructurallyEqual(ca->type, cb->type);
    }
    return false;
}

// Anti-unify `written` (the last prefix term) against `general`: walk the
// two trees in parallel; where they agree structurally, keep the node;
// where they diverge, emit the index identifier and record the
// (written-side, general-side) pair. The caller checks all pairs agree.
SurfaceExpressionPointer surfaceAntiUnify(
        const SurfaceExpressionPointer& written,
        const SurfaceExpressionPointer& general,
        const std::string& indexName,
        std::vector<std::pair<SurfaceExpressionPointer,
                              SurfaceExpressionPointer>>& pairs) {
    auto diverge = [&]() {
        pairs.push_back({written, general});
        return makeSurfaceIdentifier(indexName, {}, general->line,
                                     general->column);
    };
    if (auto* pa = std::get_if<SurfaceApplication>(&written->node)) {
        auto* pb = std::get_if<SurfaceApplication>(&general->node);
        if (pb && pa->arguments.size() == pb->arguments.size()
            && surfaceStructurallyEqual(pa->function, pb->function)) {
            bool namesMatch = true;
            for (size_t i = 0; i < pa->arguments.size(); ++i) {
                if (pa->arguments[i].name != pb->arguments[i].name) {
                    namesMatch = false;
                }
            }
            if (namesMatch) {
                std::vector<SurfaceArgument> newArguments;
                for (size_t i = 0; i < pa->arguments.size(); ++i) {
                    newArguments.push_back(SurfaceArgument{
                        pa->arguments[i].name,
                        surfaceAntiUnify(pa->arguments[i].value,
                                          pb->arguments[i].value,
                                          indexName, pairs)});
                }
                return makeSurfaceApplication(
                    pb->function, std::move(newArguments),
                    general->line, general->column);
            }
        }
        return diverge();
    }
    if (auto* oa = std::get_if<SurfaceBinaryOperation>(&written->node)) {
        auto* ob = std::get_if<SurfaceBinaryOperation>(&general->node);
        if (ob && oa->opSymbol == ob->opSymbol) {
            auto left = surfaceAntiUnify(oa->left, ob->left,
                                          indexName, pairs);
            auto right = surfaceAntiUnify(oa->right, ob->right,
                                           indexName, pairs);
            return makeSurfaceBinaryOperation(
                ob->opSymbol, std::move(left), std::move(right),
                general->line, general->column);
        }
        return diverge();
    }
    if (auto* ua = std::get_if<SurfaceUnaryOperation>(&written->node)) {
        auto* ub = std::get_if<SurfaceUnaryOperation>(&general->node);
        if (ub && ua->opSymbol == ub->opSymbol) {
            return makeSurfaceUnaryOperation(
                ub->opSymbol,
                surfaceAntiUnify(ua->operand, ub->operand,
                                  indexName, pairs),
                general->line, general->column);
        }
        return diverge();
    }
    if (surfaceStructurallyEqual(written, general)) return general;
    return diverge();
}

// Every identifier occurring in a surface tree (for fresh-name choice and
// probe-candidate collection).
void collectSurfaceIdentifiers(const SurfaceExpressionPointer& node,
                               std::vector<std::string>& out) {
    if (auto* identifier = std::get_if<SurfaceIdentifier>(&node->node)) {
        out.push_back(identifier->qualifiedName);
        return;
    }
    if (auto* application = std::get_if<SurfaceApplication>(&node->node)) {
        collectSurfaceIdentifiers(application->function, out);
        for (const auto& argument : application->arguments) {
            collectSurfaceIdentifiers(argument.value, out);
        }
        return;
    }
    if (auto* binary = std::get_if<SurfaceBinaryOperation>(&node->node)) {
        collectSurfaceIdentifiers(binary->left, out);
        collectSurfaceIdentifiers(binary->right, out);
        return;
    }
    if (auto* unary = std::get_if<SurfaceUnaryOperation>(&node->node)) {
        collectSurfaceIdentifiers(unary->operand, out);
        return;
    }
    if (auto* ascription = std::get_if<SurfaceAscription>(&node->node)) {
        collectSurfaceIdentifiers(ascription->expression, out);
        collectSurfaceIdentifiers(ascription->type, out);
        return;
    }
}

// Minimal surface renderer for recognizer diagnostics (the node subset
// the ellipsis notation can contain).
std::string surfaceToDisplayString(const SurfaceExpressionPointer& node) {
    if (auto* identifier = std::get_if<SurfaceIdentifier>(&node->node)) {
        return identifier->qualifiedName;
    }
    if (auto* numeral = std::get_if<SurfaceNumericLiteral>(&node->node)) {
        return numeral->digits;
    }
    if (auto* application = std::get_if<SurfaceApplication>(&node->node)) {
        std::string rendered =
            surfaceToDisplayString(application->function) + "(";
        for (size_t i = 0; i < application->arguments.size(); ++i) {
            if (i) rendered += ", ";
            rendered += surfaceToDisplayString(
                application->arguments[i].value);
        }
        return rendered + ")";
    }
    if (auto* binary = std::get_if<SurfaceBinaryOperation>(&node->node)) {
        return "(" + surfaceToDisplayString(binary->left) + " "
            + binary->opSymbol + " "
            + surfaceToDisplayString(binary->right) + ")";
    }
    if (auto* unary = std::get_if<SurfaceUnaryOperation>(&node->node)) {
        return unary->opSymbol + surfaceToDisplayString(unary->operand);
    }
    if (auto* ascription = std::get_if<SurfaceAscription>(&node->node)) {
        return "(" + surfaceToDisplayString(ascription->expression) + " : "
            + surfaceToDisplayString(ascription->type) + ")";
    }
    return "<expression>";
}

// Ground evaluation directly on the SURFACE tree (numerals and the
// arithmetic operators, `-` read as monus). This is what lets a probe
// instance like `2*1 - 1` verify even though `-` has no Natural
// elaboration — the ellipsis display is notation, evaluated as
// blackboard arithmetic.
std::optional<unsigned long long> surfaceGroundEval(
        const SurfaceExpressionPointer& node) {
    if (auto* numeral = std::get_if<SurfaceNumericLiteral>(&node->node)) {
        try { return std::stoull(numeral->digits); }
        catch (...) { return std::nullopt; }
    }
    if (auto* binary = std::get_if<SurfaceBinaryOperation>(&node->node)) {
        auto a = surfaceGroundEval(binary->left);
        auto b = surfaceGroundEval(binary->right);
        if (!a || !b) return std::nullopt;
        if (binary->opSymbol == "+") return *a + *b;
        if (binary->opSymbol == "*") return *a * *b;
        if (binary->opSymbol == "-") return *a >= *b ? *a - *b : 0;
        if (binary->opSymbol == "^") {
            unsigned long long result = 1;
            for (unsigned long long i = 0; i < *b; ++i) result *= *a;
            return result;
        }
        return std::nullopt;
    }
    return std::nullopt;
}

// The probe verifies instances under blackboard-monus semantics for
// `-`; the desugared body must spell that same semantics in a form the
// carrier elaborates — Natural.monus.
SurfaceExpressionPointer monusizeSurface(
        const SurfaceExpressionPointer& node) {
    if (auto* binary = std::get_if<SurfaceBinaryOperation>(&node->node)) {
        auto left = monusizeSurface(binary->left);
        auto right = monusizeSurface(binary->right);
        if (binary->opSymbol == "-") {
            return makeSurfaceApplication(
                makeSurfaceIdentifier("Natural.monus", {},
                                      node->line, node->column),
                std::vector<SurfaceExpressionPointer>{left, right},
                node->line, node->column);
        }
        return makeSurfaceBinaryOperation(
            binary->opSymbol, std::move(left), std::move(right),
            node->line, node->column);
    }
    if (auto* application = std::get_if<SurfaceApplication>(&node->node)) {
        std::vector<SurfaceArgument> newArguments;
        for (const auto& argument : application->arguments) {
            newArguments.push_back(SurfaceArgument{
                argument.name, monusizeSurface(argument.value)});
        }
        return makeSurfaceApplication(
            application->function, std::move(newArguments),
            node->line, node->column);
    }
    if (auto* unary = std::get_if<SurfaceUnaryOperation>(&node->node)) {
        return makeSurfaceUnaryOperation(
            unary->opSymbol, monusizeSurface(unary->operand),
            node->line, node->column);
    }
    return node;
}

// Numeral-literal probe helpers.
std::optional<unsigned long long> surfaceNumeralValue(
        const SurfaceExpressionPointer& node) {
    auto* numeral = std::get_if<SurfaceNumericLiteral>(&node->node);
    if (!numeral) return std::nullopt;
    try {
        return std::stoull(numeral->digits);
    } catch (...) { return std::nullopt; }
}

} // namespace

bool Elaborator::ellipsisTermsMatch(
        const SurfaceExpressionPointer& written,
        const SurfaceExpressionPointer& expected,
        ExpressionPointer carrierType,
        const std::vector<LocalBinder>& localBinders) {
    // Blackboard arithmetic first: if both sides ground-evaluate at the
    // surface level, compare numbers (this also covers spellings with no
    // Natural elaboration, like a probe instance `2*1 - 1`).
    {
        auto writtenValue = surfaceGroundEval(written);
        auto expectedValue = surfaceGroundEval(expected);
        if (writtenValue && expectedValue) {
            return *writtenValue == *expectedValue;
        }
    }
    ExpressionPointer writtenKernel, expectedKernel;
    try {
        writtenKernel = elaborateExpression(
            *written, localBinders, carrierType);
        expectedKernel = elaborateExpression(
            *expected, localBinders, carrierType);
    } catch (const ElaborateError&) {
        return false;
    } catch (const TypeError&) {
        return false;
    } catch (const AutoProverBudgetError&) {
        return false;
    }
    size_t N = localBinders.size();
    try {
        Context context = buildContextFromLocalBinders(localBinders);
        if (isDefinitionallyEqual(
                environment_, context,
                openOverLocalBinders(writtenKernel, localBinders, N),
                openOverLocalBinders(expectedKernel, localBinders, N))) {
            return true;
        }
    } catch (...) { /* fall through to ground evaluation */ }
    auto writtenValue = evaluateGroundNatural(writtenKernel);
    auto expectedValue = evaluateGroundNatural(expectedKernel);
    if (writtenValue && expectedValue) {
        return *writtenValue == *expectedValue;
    }
    // Final tier — one pass of registered characterizing equations, as a
    // budget-capped bare-prover probe on the equality (§3: what lets
    // `x ≡ x^1` verify against opaque `power` via the automatic
    // power_one). Truth-only: the proof term is discarded.
    try {
        RedundancyBudgetGuard budgetGuard(*this);
        LevelPointer universe = typeUniverseOf(localBinders, writtenKernel);
        ExpressionPointer equality = makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality", {universe}), carrierType),
                writtenKernel),
            expectedKernel);
        ExpressionPointer proof =
            autoProveClaim(equality, localBinders, written->line);
        return proof != nullptr;
    } catch (const ElaborateError&) {
    } catch (const TypeError&) {
    } catch (const AutoProverBudgetError&) {
    }
    return false;
}

ExpressionPointer Elaborator::elaborateEllipsisFold(
        const SurfaceEllipsisFold& fold,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this, "ellipsis fold (… " + fold.operatorSymbol
                    + " ... " + fold.operatorSymbol + " …) at line "
                    + std::to_string(line));
        size_t k = fold.prefixTerms.size();
        const SurfaceExpressionPointer& general = fold.generalTerm;
        const SurfaceExpressionPointer& last = fold.prefixTerms[k - 1];

        // NOTE: the general term is never elaborated verbatim — a
        // half-open display like `a(n - 1)` contains the bound-only
        // `E - 1` syntax, which has no Natural elaboration. The carrier
        // comes from the ABSTRACTED term function (mechanism 1) or a
        // numeral-substituted instance (mechanism 2).
        auto carrierOfBody = [&](const SurfaceExpressionPointer& body)
                -> ExpressionPointer {
            ExpressionPointer bodyKernel = elaborateExpression(
                *body, localBinders);
            return closeOverLocalBinders(
                inferTypeInLocalContext(localBinders, bodyKernel),
                localBinders, localBinders.size());
        };

        // A fresh index name: prefer `k`, avoid capture against anything
        // spelled in the general term or bound in scope.
        std::vector<std::string> usedNames;
        collectSurfaceIdentifiers(general, usedNames);
        for (const auto& binder : localBinders) {
            usedNames.push_back(binder.name);
        }
        auto isUsed = [&](const std::string& candidate) {
            for (const auto& name : usedNames) {
                if (name == candidate) return true;
            }
            return false;
        };
        std::string indexName = "k";
        for (int suffix = 0; isUsed(indexName); ++suffix) {
            indexName = "k" + std::to_string(suffix);
        }

        // Index spelling at offset i above lo, canonical: ground numerals
        // fold; symbolic lo keeps `lo` (i = 0) or `lo + i`.
        auto indexAt = [&](const SurfaceExpressionPointer& lo, size_t i)
                -> SurfaceExpressionPointer {
            if (auto loValue = surfaceNumeralValue(lo)) {
                return makeSurfaceNumericLiteral(
                    std::to_string(*loValue + i), line, column);
            }
            if (i == 0) return lo;
            return makeSurfaceBinaryOperation(
                "+", lo, makeSurfaceNumericLiteral(
                    std::to_string(i), line, column), line, column);
        };

        // Shared: verify the earlier prefix terms against f at lo…; a
        // mismatch records the nearest-miss detail and declines (the 0/1
        // probe may still read the shape — e.g. `2 + 4 + ... + 2*n`,
        // where anti-unification's whole-term candidate f = ⟨index⟩
        // verifies false and the probe finds f(1) = 2).
        std::string mismatchDetail;
        auto verifyAndFinish = [&](const SurfaceExpressionPointer& fBody,
                          const SurfaceExpressionPointer& lo,
                          const SurfaceExpressionPointer& hi,
                          ExpressionPointer carrierType)
                -> ExpressionPointer {
            for (size_t i = 0; i + 1 < k; ++i) {
                SurfaceExpressionPointer expected = substituteSurfaceIdentifier(
                    fBody, indexName, indexAt(lo, i));
                if (!ellipsisTermsMatch(fold.prefixTerms[i], expected,
                                         carrierType, localBinders)) {
                    mismatchDetail = "candidate term function `"
                        + surfaceToDisplayString(fBody) + "` (index `"
                        + indexName + "`, start `"
                        + surfaceToDisplayString(lo) + "`) generates `"
                        + surfaceToDisplayString(expected) + "` at term "
                        + std::to_string(i + 1) + ", but the prefix has `"
                        + surfaceToDisplayString(fold.prefixTerms[i]) + "`";
                    return nullptr;
                }
            }
            SurfaceFoldBinder binder{fold.operatorSymbol, indexName,
                                      lo, hi, fBody};
            return elaborateFoldBinder(binder, localBinders, expectedType,
                                        line, column);
        };

        // Mechanism 1 — anti-unification against the last prefix term.
        // A reading verified against at least one earlier prefix term is
        // decisive. The degenerate case — a SINGLE prefix term diverging
        // at the ROOT (candidate f = the bare index, which any display
        // matches) — is only a candidate: it competes with the probe's
        // readings and an overlap is the §9 ambiguity error
        // (`0 + ... + k*(k−1)`).
        SurfaceExpressionPointer identityReadingLo, identityReadingHi;
        {
            std::vector<std::pair<SurfaceExpressionPointer,
                                  SurfaceExpressionPointer>> pairs;
            SurfaceExpressionPointer fBody = surfaceAntiUnify(
                last, general, indexName, pairs);
            bool consistent = !pairs.empty();
            for (size_t i = 1; i < pairs.size() && consistent; ++i) {
                consistent = surfaceStructurallyEqual(pairs[i].first,
                                                      pairs[0].first)
                    && surfaceStructurallyEqual(pairs[i].second,
                                                pairs[0].second);
            }
            bool rootDiffSingleTerm = consistent && k == 1
                && pairs.size() == 1
                && std::get_if<SurfaceIdentifier>(&fBody->node) != nullptr;
            if (consistent && !rootDiffSingleTerm) {
                const SurfaceExpressionPointer& lastIndex = pairs[0].first;
                const SurfaceExpressionPointer& hi = pairs[0].second;
                // Carrier from the LAST WRITTEN TERM (fully concrete —
                // the abstracted body would need the binder in scope).
                ExpressionPointer carrierType = carrierOfBody(last);
                // lo := lastIndex − (k − 1), by numeral arithmetic on the
                // literal or on a trailing `+ numeral`.
                SurfaceExpressionPointer lo;
                if (k == 1) {
                    lo = lastIndex;
                } else if (auto lastValue = surfaceNumeralValue(lastIndex)) {
                    if (*lastValue >= k - 1) {
                        lo = makeSurfaceNumericLiteral(
                            std::to_string(*lastValue - (k - 1)),
                            line, column);
                    }
                } else if (auto* sum = std::get_if<SurfaceBinaryOperation>(
                               &lastIndex->node)) {
                    if (sum->opSymbol == "+") {
                        if (auto offset = surfaceNumeralValue(sum->right)) {
                            if (*offset >= k - 1) {
                                lo = *offset == k - 1
                                    ? sum->left
                                    : makeSurfaceBinaryOperation(
                                          "+", sum->left,
                                          makeSurfaceNumericLiteral(
                                              std::to_string(
                                                  *offset - (k - 1)),
                                              line, column),
                                          line, column);
                            }
                        }
                    }
                }
                if (lo) {
                    if (ExpressionPointer result =
                            verifyAndFinish(fBody, lo, hi, carrierType)) {
                        return result;
                    }
                }
            }
            if (rootDiffSingleTerm) {
                identityReadingLo = pairs[0].first;
                identityReadingHi = pairs[0].second;
            }
        }

        // Mechanism 2 — the 0/1 evaluation probe. Candidates: identifiers
        // of the general term bound in scope at type Natural.
        struct ProbeCandidate {
            std::string variable;
            unsigned long long start;
        };
        std::vector<ProbeCandidate> survivors;
        {
            std::vector<std::string> identifiers;
            collectSurfaceIdentifiers(general, identifiers);
            std::sort(identifiers.begin(), identifiers.end());
            identifiers.erase(
                std::unique(identifiers.begin(), identifiers.end()),
                identifiers.end());
            for (const auto& name : identifiers) {
                bool isNaturalBinder = false;
                for (const auto& binder : localBinders) {
                    if (binder.name == name
                        && headConstantName(binder.type) == "Natural") {
                        isNaturalBinder = true;
                        break;
                    }
                }
                if (!isNaturalBinder) continue;
                for (unsigned long long start : {0ull, 1ull}) {
                    // The probe is arithmetic-anchored: instances are
                    // compared by GROUND EVALUATION, so the carrier is
                    // Natural by construction (an all-numeral instance
                    // like `2 * 1` has no bottom-up carrier otherwise).
                    ExpressionPointer carrierType = makeConstant("Natural");
                    bool allMatch = true;
                    for (size_t i = 0; i < k && allMatch; ++i) {
                        SurfaceExpressionPointer expected =
                            substituteSurfaceIdentifier(
                                general, name,
                                makeSurfaceNumericLiteral(
                                    std::to_string(start + i),
                                    line, column));
                        allMatch = ellipsisTermsMatch(
                            fold.prefixTerms[i], expected, carrierType,
                            localBinders);
                    }
                    if (allMatch) survivors.push_back({name, start});
                }
            }
        }
        // The identity reading (whole-term diff, single prefix) joins the
        // candidate pool unless a probe survivor IS the same reading
        // (bare-variable general term, same start).
        bool identityDistinct = false;
        if (identityReadingLo) {
            identityDistinct = true;
            auto* hiIdentifier = identityReadingHi
                ? std::get_if<SurfaceIdentifier>(&identityReadingHi->node)
                : nullptr;
            for (const auto& candidate : survivors) {
                if (hiIdentifier
                    && hiIdentifier->qualifiedName == candidate.variable
                    && surfaceNumeralValue(identityReadingLo)
                    && *surfaceNumeralValue(identityReadingLo)
                           == candidate.start) {
                    identityDistinct = false;
                }
            }
        }
        if (identityReadingLo && identityDistinct && !survivors.empty()) {
            std::string listing = "whole-term index (lo `"
                + surfaceToDisplayString(identityReadingLo) + "`, hi `"
                + surfaceToDisplayString(identityReadingHi) + "`)";
            for (const auto& candidate : survivors) {
                listing += "; index `" + candidate.variable + "` (start "
                    + std::to_string(candidate.start) + ")";
            }
            throwElaborate(
                "ambiguous ellipsis: " + listing + " all generate the "
                "written prefix — write one more prefix term to pin the "
                "start, or use the explicit form "
                "(sum k from LO to HI of BODY)");
        }
        if (identityReadingLo && survivors.empty()) {
            // Unambiguous after all: only the identity reading exists.
            ExpressionPointer carrierType = carrierOfBody(last);
            SurfaceExpressionPointer fBody = makeSurfaceIdentifier(
                indexName, {}, line, column);
            if (ExpressionPointer result = verifyAndFinish(
                    fBody, identityReadingLo, identityReadingHi,
                    carrierType)) {
                return result;
            }
        }
        if (survivors.size() == 1) {
            const auto& winner = survivors[0];
            SurfaceExpressionPointer lo = makeSurfaceNumericLiteral(
                std::to_string(winner.start), line, column);
            SurfaceExpressionPointer hi = makeSurfaceIdentifier(
                winner.variable, {}, line, column);
            // The prefix was already verified by the probe; the binder
            // name is the variable itself (bounds elaborate outside the
            // binder, so the outer occurrence is not captured). `-` in
            // the general term was verified as blackboard monus — spell
            // it as Natural.monus so the body elaborates.
            SurfaceFoldBinder binder{fold.operatorSymbol, winner.variable,
                                      lo, hi, monusizeSurface(general)};
            return elaborateFoldBinder(binder, localBinders, expectedType,
                                        line, column);
        }
        if (survivors.size() > 1) {
            std::string listing;
            for (const auto& candidate : survivors) {
                if (!listing.empty()) listing += "; ";
                listing += "index `" + candidate.variable + "` (start "
                    + std::to_string(candidate.start) + ")";
            }
            throwElaborate(
                "ambiguous ellipsis: " + listing + " all generate the "
                "written prefix — write one more prefix term to pin the "
                "start, or use the explicit form "
                "(sum k from LO to HI of BODY)");
        }
        throwElaborate(
            "could not read the ellipsis: the general term `"
            + surfaceToDisplayString(general)
            + "` neither anti-unifies with the last prefix term `"
            + surfaceToDisplayString(last)
            + "` at one consistent position, nor generates the prefix "
            "from a Natural index at start 0 or 1."
            + (mismatchDetail.empty() ? std::string()
                                       : "\n    " + mismatchDetail)
            + "\n    Write the explicit form "
            "(sum k from LO to HI of BODY)");
    }

ExpressionPointer Elaborator::elaborateSeriesRelation(
        const SurfaceSeriesFold& series,
        const SurfaceExpressionPointer& otherSide,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this, "series relation (… " + series.operatorSymbol
                    + " ... = …) at line " + std::to_string(line));
        if (series.operatorSymbol != "+") {
            throwElaborate(
                "series relations are defined for `+` (sums at Real) in "
                "this version; found `" + series.operatorSymbol + "`");
        }
        size_t k = series.prefixTerms.size();
        const SurfaceExpressionPointer& last = series.prefixTerms[k - 1];
        const SurfaceExpressionPointer& general = series.generalTerm;

        // Fresh index and partial-fold-count names.
        std::vector<std::string> usedNames;
        collectSurfaceIdentifiers(general, usedNames);
        for (const auto& term : series.prefixTerms) {
            collectSurfaceIdentifiers(term, usedNames);
        }
        for (const auto& binder : localBinders) {
            usedNames.push_back(binder.name);
        }
        auto isUsed = [&](const std::string& candidate) {
            for (const auto& name : usedNames) {
                if (name == candidate) return true;
            }
            return false;
        };
        std::string indexName = "k";
        for (int suffix = 0; isUsed(indexName); ++suffix) {
            indexName = "k" + std::to_string(suffix);
        }
        std::string countName = "N";
        for (int suffix = 0;
             isUsed(countName) || countName == indexName; ++suffix) {
            countName = "N" + std::to_string(suffix);
        }

        // Recognition: mechanism 1 (structural anchors) only in this
        // version — the series' index is typically a display-only letter
        // with no binding, so the probe's in-scope-candidate story does
        // not apply.
        std::vector<std::pair<SurfaceExpressionPointer,
                              SurfaceExpressionPointer>> pairs;
        SurfaceExpressionPointer fBody = surfaceAntiUnify(
            last, general, indexName, pairs);
        bool consistent = !pairs.empty();
        for (size_t i = 1; i < pairs.size() && consistent; ++i) {
            consistent = surfaceStructurallyEqual(pairs[i].first,
                                                  pairs[0].first)
                && surfaceStructurallyEqual(pairs[i].second,
                                            pairs[0].second);
        }
        if (!consistent) {
            throwElaborate(
                "could not read the series: the general term `"
                + surfaceToDisplayString(general)
                + "` does not anti-unify with the last written term `"
                + surfaceToDisplayString(last)
                + "` at one consistent position. Spell the terms so the "
                "index positions line up (e.g. `1/2 + 1/4 + ... + "
                "1/Real.power(k, 2) + ...` with explicit prefix "
                "spellings)");
        }
        // lo := lastIndex − (k − 1), and only literal 0/1 in this version
        // (those are the monus-free partial-fold counts).
        SurfaceExpressionPointer lo;
        const SurfaceExpressionPointer& lastIndex = pairs[0].first;
        if (k == 1) {
            lo = lastIndex;
        } else if (auto lastValue = surfaceNumeralValue(lastIndex)) {
            if (*lastValue >= k - 1) {
                lo = makeSurfaceNumericLiteral(
                    std::to_string(*lastValue - (k - 1)), line, column);
            }
        }
        auto loValue = lo ? surfaceNumeralValue(lo) : std::nullopt;
        if (!loValue || *loValue > 1) {
            throwElaborate(
                "series lower bounds are literal 0 or 1 in this version "
                "(the display's first term must sit at index 0 or 1)");
        }
        // Verify the earlier written terms at Real.
        ExpressionPointer realType = makeConstant("Real");
        for (size_t i = 0; i + 1 < k; ++i) {
            SurfaceExpressionPointer expected = substituteSurfaceIdentifier(
                fBody, indexName,
                makeSurfaceNumericLiteral(std::to_string(*loValue + i),
                                          line, column));
            if (!ellipsisTermsMatch(series.prefixTerms[i], expected,
                                     realType, localBinders)) {
                throwElaborate(
                    "the series' general term does not generate the "
                    "written prefix: term " + std::to_string(i + 1)
                    + " should be `" + surfaceToDisplayString(expected)
                    + "` but the display has `"
                    + surfaceToDisplayString(series.prefixTerms[i]) + "`");
            }
        }
        // Target predicate.
        bool toInfinity = false;
        if (auto* identifier =
                std::get_if<SurfaceIdentifier>(&otherSide->node)) {
            toInfinity = identifier->qualifiedName == "infinity"
                || identifier->qualifiedName == "∞";
        }
        const char* target = toInfinity
            ? "Real.TendsToInfinity" : "Real.SequenceConverges";
        if (!environment_.lookup(target)) {
            throwElaborate(std::string("a series relation elaborates to `")
                + target + "` — import "
                + (toInfinity ? "Real.limits" : "Real.convergence"));
        }
        // λ(N : Natural). the partial fold of N terms: at lo = 1 the
        // inclusive binder-form upper bound N gives count N; at lo = 0
        // the half-open `N - 1` does.
        SurfaceExpressionPointer hi = *loValue == 1
            ? makeSurfaceIdentifier(countName, {}, line, column)
            : makeSurfaceBinaryOperation(
                  "-", makeSurfaceIdentifier(countName, {}, line, column),
                  makeSurfaceNumericLiteral("1", line, column),
                  line, column);
        SurfaceExpressionPointer foldSurface = makeSurfaceFoldBinder(
            series.operatorSymbol, indexName, lo, hi, fBody, line, column);
        SurfaceBinder countBinder{
            {countName},
            makeSurfaceIdentifier("Natural", {}, line, column), false};
        SurfaceExpressionPointer sequence = makeSurfaceLambda(
            countBinder, foldSurface, line, column);
        std::vector<SurfaceExpressionPointer> arguments{sequence};
        if (!toInfinity) arguments.push_back(otherSide);
        SurfaceExpressionPointer call = makeSurfaceApplication(
            makeSurfaceIdentifier(target, {}, line, column),
            std::move(arguments), line, column);
        return elaborateExpression(*call, localBinders, expectedType);
    }

// Out-of-line Elaborator method definitions: arithmetic-operator desugaring + reflexivity/symmetry/transitivity desugaring + extractEqualityComponents
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::desugarArithmeticOperator(
        const std::string& operatorSymbol,
        const SurfaceExpression& leftSurface,
        const SurfaceExpression& rightSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {
        // First: if a local binder has the operator symbol as its
        // name (introduced via `((·) : G → G → G)`-style binders),
        // treat the operator as an application of that binder. This
        // lets group/ring theorems use `x · y` for the bound
        // operation without having to plumb it through the global
        // operator registry.
        for (size_t i = localBinders.size(); i > 0; --i) {
            if (localBinders[i - 1].name == operatorSymbol) {
                ExpressionPointer leftLocal =
                    elaborateExpression(leftSurface, localBinders);
                ExpressionPointer rightLocal =
                    elaborateExpression(rightSurface, localBinders);
                ExpressionPointer functionExpression =
                    elaborateIdentifier(
                        SurfaceIdentifier{operatorSymbol, {}},
                        localBinders, line, /*column=*/0);
                ExpressionPointer call = makeApplication(
                    std::move(functionExpression), std::move(leftLocal));
                call = makeApplication(std::move(call),
                                        std::move(rightLocal));
                return call;
            }
        }
        // `≥` and `>` desugar to the flipped `≤`/`<` against the same
        // carrier. We never register a separate function for them — the
        // existing `≤`/`<` registry entries are reused with the operand
        // order reversed. This keeps a single source of truth for the
        // order relation and lets calc chains mix the two notations.
        if (operatorSymbol == "≥") {
            return desugarArithmeticOperator(
                "≤", rightSurface, leftSurface, localBinders,
                expectedType, line);
        }
        if (operatorSymbol == ">") {
            return desugarArithmeticOperator(
                "<", rightSurface, leftSurface, localBinders,
                expectedType, line);
        }
        // Logical operators are dispatched first because their operand
        // type is a Proposition (a `Sort`, not a `Constant`), so the
        // numeric-operator dispatch below — which looks for a Constant
        // head on the inferred operand type — wouldn't see them.
        std::string logicalTarget;
        if (operatorSymbol == "∧") logicalTarget = "And";
        else if (operatorSymbol == "∨") logicalTarget = "Or";
        if (!logicalTarget.empty()) {
            if (environment_.lookup(logicalTarget) == nullptr) {
                throw ElaborateError(
                    "operator '" + operatorSymbol + "' resolves to '"
                    + logicalTarget + "' but that inductive is not in "
                    "scope (line " + std::to_string(line)
                    + "); import Logic.basics");
            }
            ExpressionPointer leftLogical =
                elaborateExpression(leftSurface, localBinders);
            ExpressionPointer rightLogical =
                elaborateExpression(rightSurface, localBinders);
            ExpressionPointer call = makeConstant(logicalTarget);
            call = makeApplication(std::move(call), std::move(leftLogical));
            call = makeApplication(std::move(call), std::move(rightLogical));
            return call;
        }
        // Use the outer expected type as a hint for the LEFT operand
        // only when it's a Constant head — e.g. `Rational`, `Integer`,
        // `Real`, `PAdic`. For arithmetic operators like `+`, `*`,
        // `-`, the result type equals the operand type, so the hint
        // is exactly the operand type. For `≤`, `<`, etc. the result
        // type is `Proposition` (a Sort, not a Constant), so the
        // guard skips them. Lets short-form `Quotient.mk(rep)` fire
        // on the LEFT of a homogeneous operator when the outer
        // context provides the carrier head.
        ExpressionPointer leftExpectedType = nullptr;
        if (expectedType
            && std::holds_alternative<Constant>(expectedType->node)) {
            leftExpectedType = expectedType;
        }
        ExpressionPointer leftKernel =
            elaborateExpression(leftSurface, localBinders,
                                 leftExpectedType);
        // Determine the operand type by inferring the type of the left
        // operand. Check the raw inferred type first: if a binder was
        // declared with a named type like `Integer` (which δ-reduces
        // to `Quotient(IntegerRepresentative, IntegerEquivalent)`),
        // we want to dispatch on `Integer`, not the unfolded form.
        // Only WHNF as a fallback for types that are themselves
        // computations (rare in practice but used by let-bindings
        // whose type-annotation is a reducible expression).
        ExpressionPointer leftTypeRaw =
            inferTypeInLocalContext(localBinders, leftKernel);
        // Propagate the left operand's type as expected type for the
        // right operand. This lets short-form `Quotient.mk(rep)` (with
        // R inferred from expected type) fire in operand position of
        // homogeneous operators like `+`, `*`, `≤`, `<` on Rational,
        // Real, etc. — mirrors the `=` desugaring's identical trick.
        ExpressionPointer leftTypeClosed = closeOverLocalBinders(
            leftTypeRaw, localBinders, localBinders.size());
        ExpressionPointer rightKernel =
            elaborateExpression(rightSurface, localBinders,
                                 leftTypeClosed);
        // Use `headConstantName` to extract the type head — peels through
        // Applications so parameterised types like `Set(T)` report `Set`
        // and `Quotient(IR, IE)` reports `Quotient`. Falls back to WHNF
        // for definitional aliases whose RHS exposes a different head.
        std::string operandTypeName = headConstantName(leftTypeRaw);
        std::string targetFunction;
        // First consult the user-declared registry: any
        // `operator (sym) on (T1, T2) := F;` registration wins. This is
        // the extensible path — Rational, Real, Complex, polynomial
        // rings, etc. all hook in here. Wildcard `_` registrations
        // (e.g. `∈` on `(_, Set)`) match any LHS or RHS type.
        ExpressionPointer rightTypeRaw =
            inferTypeInLocalContext(localBinders, rightKernel);
        std::string rightTypeName = headConstantName(rightTypeRaw);
        std::string registered = environment_.lookupOperator(
            operatorSymbol, operandTypeName, rightTypeName);
        if (!registered.empty()) {
            targetFunction = registered;
        }
        // Fallback: if the raw head Constant didn't match anything,
        // try operand-type names from the registry whose definition
        // δ-reduces to the operand's actual type. This catches
        // `Quotient.mk(IntegerRepresentative, IntegerEquivalent, _)`
        // (raw type head: `Quotient`) being treated as `Integer`
        // (whose definition body is exactly that `Quotient(...)`).
        if (targetFunction.empty()) {
            ExpressionPointer operandLeftWHNF = weakHeadNormalForm(
                environment_, leftTypeRaw);
            ExpressionPointer operandRightWHNF = weakHeadNormalForm(
                environment_, rightTypeRaw);
            for (const auto& [key, funcName]
                 : environment_.operatorRegistry) {
                const auto& [opSym, leftReg, rightReg] = key;
                if (opSym != operatorSymbol) continue;
                const Declaration* leftDecl =
                    environment_.lookup(leftReg);
                const Declaration* rightDecl =
                    environment_.lookup(rightReg);
                auto* leftDef = leftDecl
                    ? std::get_if<Definition>(leftDecl) : nullptr;
                auto* rightDef = rightDecl
                    ? std::get_if<Definition>(rightDecl) : nullptr;
                if (!leftDef || !rightDef) continue;
                ExpressionPointer leftRegBodyWHNF = weakHeadNormalForm(
                    environment_, leftDef->body);
                ExpressionPointer rightRegBodyWHNF = weakHeadNormalForm(
                    environment_, rightDef->body);
                if (structurallyEqual(leftRegBodyWHNF, operandLeftWHNF)
                    && structurallyEqual(rightRegBodyWHNF,
                                            operandRightWHNF)) {
                    targetFunction = funcName;
                    break;
                }
            }
        }
        // Alias fallback: the operand type may be a definition that
        // abbreviates a registered type — e.g. `GaussianInteger :=
        // RingModulo(…)`, `ComplexNumber := RingModulo(…)`. Unfold each
        // operand type's head one δ-step at a time, collecting the heads it
        // passes through, and retry the registry over those. A SINGLE-step
        // unfold (not full WHNF) is essential: `RingModulo` is itself a
        // definition for `Quotient(…)`, so WHNF would blow past the
        // `RingModulo` registration all the way to `Quotient`. We try the
        // raw head first (already done above), then successive unfoldings,
        // so an alias dispatches exactly like the type it names.
        if (targetFunction.empty()) {
            auto collectHeads = [&](ExpressionPointer typeExpr) {
                std::vector<std::string> heads;
                ExpressionPointer current = typeExpr;
                for (int step = 0; step < 64; ++step) {
                    current = unfoldHeadConstantOneStep(current);
                    if (!current) break;
                    std::string head = headConstantName(current);
                    if (!head.empty()) heads.push_back(head);
                }
                return heads;
            };
            std::vector<std::string> leftHeads = collectHeads(leftTypeRaw);
            std::vector<std::string> rightHeads = collectHeads(rightTypeRaw);
            leftHeads.insert(leftHeads.begin(), operandTypeName);
            rightHeads.insert(rightHeads.begin(), rightTypeName);
            // Reverse-alias enrichment: an operand can arrive with its
            // type ALREADY normalised (a recursive self-reference in a
            // pattern-definition body gets the declared return type
            // reduced, so `ComplexNumber` shows up as `Quotient(…)`).
            // Then the forward unfold above finds nothing — so also scan
            // bare alias definitions whose body weak-head-normalises to
            // the operand type, and walk THEIR unfold chains (which pass
            // through the registered head, e.g. `RingModulo`, before the
            // quotient underneath).
            auto reverseAliasHeads =
                [&](ExpressionPointer typeRaw) {
                std::vector<std::string> heads;
                ExpressionPointer typeWHNF = weakHeadNormalForm(
                    environment_, typeRaw);
                for (const auto& [name, declaration]
                     : environment_.declarations) {
                    auto* definition =
                        std::get_if<Definition>(&declaration);
                    if (!definition
                        || !definition->universeParameters.empty()) {
                        continue;
                    }
                    // Bare aliases only; a parameterised definition's
                    // body is a lambda and can never match a type.
                    if (std::holds_alternative<Lambda>(
                            definition->body->node)) {
                        continue;
                    }
                    ExpressionPointer bodyWHNF = weakHeadNormalForm(
                        environment_, definition->body);
                    if (!structurallyEqual(bodyWHNF, typeWHNF)) continue;
                    heads.push_back(name);
                    ExpressionPointer cursor = definition->body;
                    for (int step = 0; step < 8; ++step) {
                        std::string head = headConstantName(cursor);
                        if (head.empty()) break;
                        if (heads.empty() || heads.back() != head) {
                            heads.push_back(head);
                        }
                        cursor = unfoldHeadConstantOneStep(cursor);
                        if (!cursor) break;
                    }
                }
                return heads;
            };
            auto tryHeadPairs = [&]() {
                for (const auto& lh : leftHeads) {
                    if (!targetFunction.empty()) break;
                    for (const auto& rh : rightHeads) {
                        if (lh.empty() || rh.empty()) continue;
                        std::string reg = environment_.lookupOperator(
                            operatorSymbol, lh, rh);
                        if (!reg.empty()) { targetFunction = reg; break; }
                    }
                }
            };
            tryHeadPairs();
            if (targetFunction.empty()) {
                for (const auto& head : reverseAliasHeads(leftTypeRaw)) {
                    leftHeads.push_back(head);
                }
                for (const auto& head : reverseAliasHeads(rightTypeRaw)) {
                    rightHeads.push_back(head);
                }
                tryHeadPairs();
            }
        }
        // Final registry fallback: WHNF the operand types to expose a
        // CONCRETE carrier head. A value whose type is a bundle projection
        // over a concrete ring — `Ring.carrier(Real.polynomial_ring)` (from
        // a `divides` existential), or `Ring.carrier(Real.ring)` — reduces
        // to the concrete carrier (`Polynomial(...)`, `Real`), so it then
        // dispatches like that concrete type. An ABSTRACT carrier
        // (`Ring.carrier(s)` for a variable `s`) stays stuck under WHNF, so
        // its bundle dispatch is unchanged. Only consulted after the
        // raw-head lookup failed, so this never overrides an existing
        // dispatch — it can only turn a mixed/projected head pair that
        // would otherwise error into a successful one.
        if (targetFunction.empty()) {
            // Resolve a carrier PROJECTION over a concrete ring to the
            // carrier field as written in the bundle's constructor (NOT
            // further reduced — full WHNF would blow past `Polynomial(…)`
            // to its underlying `Quotient(…)`). So a value typed
            // `Ring.carrier(Real.polynomial_ring)` (from a `divides`
            // existential) dispatches like `Polynomial`. An abstract
            // `Ring.carrier(s)` resolves to nothing (the bundle arg is
            // stuck), so its dispatch is unchanged.
            ExpressionPointer leftProj =
                carrierProjectionField(leftTypeRaw);
            ExpressionPointer rightProj =
                carrierProjectionField(rightTypeRaw);
            std::string leftProjHead =
                leftProj ? headConstantName(leftProj) : std::string();
            std::string rightProjHead =
                rightProj ? headConstantName(rightProj) : std::string();
            const std::string leftCandidates[2] =
                {leftProjHead, operandTypeName};
            const std::string rightCandidates[2] =
                {rightProjHead, rightTypeName};
            for (int li = 0; li < 2 && targetFunction.empty(); ++li) {
                for (int ri = 0; ri < 2 && targetFunction.empty(); ++ri) {
                    if (li == 1 && ri == 1) continue;  // raw×raw already tried
                    if (leftCandidates[li].empty()
                        || rightCandidates[ri].empty()) continue;
                    std::string reg = environment_.lookupOperator(
                        operatorSymbol, leftCandidates[li],
                        rightCandidates[ri]);
                    if (!reg.empty()) targetFunction = reg;
                }
            }
        }
        // For `<` we wrap the left operand in `successor`, since
        // `a < b` is defined as `LessOrEqual(successor(a), b)`. This is
        // special enough that we leave it built-in.
        bool wrapLeftInSuccessor = false;
        if (targetFunction.empty()) {
            if (operandTypeName == "Natural") {
                if (operatorSymbol == "≤") targetFunction = "LessOrEqual";
                else if (operatorSymbol == "<") {
                    targetFunction = "LessOrEqual";
                    wrapLeftInSuccessor = true;
                }
                else if (operatorSymbol == "∣") targetFunction = "Natural.divides";
            }
        }
        if (targetFunction.empty()) {
            throw ElaborateError(
                "operator '" + operatorSymbol + "' is not supported for "
                "operand type '" + operandTypeName + "' (line "
                + std::to_string(line)
                + "); supported: +, *, ≤, <, ∣ on Natural; +, *, - on "
                "Integer; ∧, ∨ on Proposition");
        }
        if (environment_.lookup(targetFunction) == nullptr) {
            throw ElaborateError(
                "operator '" + operatorSymbol + "' resolves to '"
                + targetFunction + "' but that function is not in scope "
                "(line " + std::to_string(line) + ")");
        }
        if (wrapLeftInSuccessor) {
            if (environment_.lookup("successor") == nullptr) {
                throw ElaborateError(
                    "operator '<' on Natural requires `successor` in scope "
                    "(line " + std::to_string(line) + ")");
            }
            leftKernel = makeApplication(
                makeConstant("successor"), std::move(leftKernel));
        }
        ExpressionPointer call = makeConstant(targetFunction);
        // Fill any leading implicit binders the dispatch function may
        // have. Two patterns are common:
        //   (a) `Set.member {T : Type(0)} (x : T) (S : Set(T))` —
        //       the implicit carrier is the LEFT operand's type T.
        //   (b) `Set.subset {T : Type(0)} (A : Set(T)) (B : Set(T))` —
        //       the implicit carrier is the *parameter* of the LEFT
        //       operand's type `Set(T)`, not `Set(T)` itself.
        // We recover the fillers by unifying the LEFT operand's type
        // against the target function's first-explicit-argument type
        // template (which has BoundVariable references to the implicit
        // binders). Works for both patterns above and any
        // structurally-decomposable shape — in particular, it doesn't
        // trip when the LEFT operand's type is itself a parameterised
        // alias like `Real = Quotient(_, _)`.
        int implicitCount =
            environment_.implicitArgumentCount(targetFunction);
        if (implicitCount > 0) {
            std::vector<ExpressionPointer> implicitBindings(implicitCount);
            bool inferredByUnification = false;
            if (const Declaration* targetDecl =
                    environment_.lookup(targetFunction)) {
                ExpressionPointer cursor = declarationType(*targetDecl);
                for (int i = 0; i < implicitCount && cursor; ++i) {
                    auto* pi = std::get_if<Pi>(&cursor->node);
                    if (!pi) { cursor = nullptr; break; }
                    cursor = pi->codomain;
                }
                if (cursor) {
                    if (auto* firstExplicit =
                            std::get_if<Pi>(&cursor->node)) {
                        // Match the dispatch function's first-explicit-arg
                        // type template against the LEFT operand's type. When
                        // that type is an alias whose head differs from the
                        // template's (e.g. operand `GaussianInteger` vs
                        // template `RingModulo(?c, ?m)`), retry against
                        // successive one-step δ-unfoldings so the implicits
                        // (`{c}{m}`) are recovered from the type the alias
                        // abbreviates. Single-step so we stop at `RingModulo`
                        // rather than blowing past it to `Quotient`.
                        ExpressionPointer leftCandidate = leftTypeClosed;
                        for (int step = 0; step < 64 && !inferredByUnification;
                             ++step) {
                            std::fill(implicitBindings.begin(),
                                      implicitBindings.end(), nullptr);
                            if (matchAgainstPattern(
                                    firstExplicit->domain, leftCandidate,
                                    implicitCount, implicitBindings)) {
                                inferredByUnification = true;
                                for (const auto& binding : implicitBindings) {
                                    if (!binding) {
                                        inferredByUnification = false;
                                        break;
                                    }
                                }
                            }
                            if (inferredByUnification) break;
                            ExpressionPointer next =
                                unfoldHeadConstantOneStep(leftCandidate);
                            if (!next) break;
                            leftCandidate = next;
                        }
                    }
                }
            }
            if (inferredByUnification) {
                // bindings[0] is the INNERMOST implicit (smallest BV
                // index from inside). Application order is outermost-
                // first, so apply in reverse.
                for (int i = implicitCount - 1; i >= 0; --i) {
                    call = makeApplication(std::move(call),
                                             implicitBindings[i]);
                }
            } else {
                // Fall back to the single-filler heuristic for
                // safety. If this fires, the kernel typecheck will
                // catch a mismatch — better than silently building a
                // wrong term.
                ExpressionPointer implicitFiller = leftTypeClosed;
                auto* leftTypeApp =
                    std::get_if<Application>(&leftTypeClosed->node);
                if (leftTypeApp) {
                    implicitFiller = leftTypeApp->argument;
                }
                for (int i = 0; i < implicitCount; ++i) {
                    call = makeApplication(std::move(call),
                                             implicitFiller);
                }
            }
        }
        call = makeApplication(std::move(call), std::move(leftKernel));
        call = makeApplication(std::move(call), std::move(rightKernel));
        return call;
    }

ExpressionPointer Elaborator::desugarReflexivity(
        SurfaceExpressionPointer subjectSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {
        ExpressionPointer subjectKernel =
            elaborateExpression(*subjectSurface, localBinders);
        ExpressionPointer subjectTypeOpened =
            inferTypeInLocalContext(localBinders, subjectKernel);
        ExpressionPointer subjectType = closeOverLocalBinders(
            subjectTypeOpened, localBinders, localBinders.size());
        LevelPointer carrierUniverseLevel =
            typeUniverseOf(localBinders, subjectKernel);
        ExpressionPointer call =
            makeConstant("reflexivity", {carrierUniverseLevel});
        call = makeApplication(std::move(call), std::move(subjectType));
        call = makeApplication(std::move(call), std::move(subjectKernel));
        (void)line; (void)column;
        return call;
    }

Elaborator::EqualityComponents Elaborator::extractEqualityComponents(
        ExpressionPointer equalityType, const char* contextLabel,
        int line) {
        // WHNF the type so a β-redex (e.g. the predicate body of an
        // Exists destructured via `obtain ⟨k, eq⟩` — the binder's
        // type starts as `(λ k'. P k')(k)`) reduces to the
        // applied-`Equality.{u}` form we expect to destructure below.
        equalityType =
            weakHeadNormalForm(environment_, equalityType);
        auto* outerApp = std::get_if<Application>(&equalityType->node);
        if (!outerApp) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type is not a fully applied Equality "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer rightEndpoint = outerApp->argument;
        auto* middleApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!middleApp) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type is not a fully applied Equality "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer leftEndpoint = middleApp->argument;
        auto* innerApp =
            std::get_if<Application>(&middleApp->function->node);
        if (!innerApp) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type is not a fully applied Equality "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer carrierType = innerApp->argument;
        auto* equalityConstant =
            std::get_if<Constant>(&innerApp->function->node);
        if (!equalityConstant
            || equalityConstant->name != "Equality"
            || equalityConstant->universeArguments.size() != 1) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type isn't an Equality.{u} (line "
                + std::to_string(line) + ")");
        }
        return {carrierType, leftEndpoint, rightEndpoint,
                equalityConstant->universeArguments[0]};
    }

ExpressionPointer Elaborator::desugarEqualitySymmetry(
        SurfaceExpressionPointer equalityProofSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {
        ExpressionPointer equalityProofKernel =
            elaborateExpression(*equalityProofSurface, localBinders);
        ExpressionPointer equalityProofType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          equalityProofKernel));
        EqualityComponents components = extractEqualityComponents(
            equalityProofType, "Equality.symmetry", line);
        ExpressionPointer carrierType = closeOverLocalBinders(
            components.carrierType, localBinders, localBinders.size());
        ExpressionPointer leftEndpoint = closeOverLocalBinders(
            components.leftEndpoint, localBinders, localBinders.size());
        ExpressionPointer rightEndpoint = closeOverLocalBinders(
            components.rightEndpoint, localBinders, localBinders.size());
        ExpressionPointer call =
            makeConstant("Equality.symmetry",
                          {components.carrierUniverseLevel});
        call = makeApplication(std::move(call), std::move(carrierType));
        call = makeApplication(std::move(call), std::move(leftEndpoint));
        call = makeApplication(std::move(call), std::move(rightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(equalityProofKernel));
        (void)column;
        return call;
    }

ExpressionPointer Elaborator::desugarEqualityTransitivity(
        SurfaceExpressionPointer firstEqualitySurface,
        SurfaceExpressionPointer secondEqualitySurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        // If the surrounding context provided an expected type
        // `Equality(carrier, A, C)`, synthesize `Equality(carrier, A, A)`
        // as the expected type for the first argument so that desugars
        // like rewrite (which need an expected type) can fire there too.
        // Otherwise the first argument elaborates without an expected
        // type, exactly as before.
        ExpressionPointer expectedForFirst;
        if (expectedType) {
            ExpressionPointer expectedOpened = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            ExpressionPointer expectedWhnf = weakHeadNormalForm(
                environment_, expectedOpened);
            EqualityComponents outerComponents;
            try {
                outerComponents = extractEqualityComponents(
                    expectedWhnf,
                    "Equality.transitivity (outer expected)", line);
                ExpressionPointer outerCarrier = closeOverLocalBinders(
                    outerComponents.carrierType,
                    localBinders, localBinders.size());
                ExpressionPointer outerLeft = closeOverLocalBinders(
                    outerComponents.leftEndpoint,
                    localBinders, localBinders.size());
                expectedForFirst = makeConstant(
                    "Equality",
                    {outerComponents.carrierUniverseLevel});
                expectedForFirst = makeApplication(
                    std::move(expectedForFirst), outerCarrier);
                expectedForFirst = makeApplication(
                    std::move(expectedForFirst), outerLeft);
                expectedForFirst = makeApplication(
                    std::move(expectedForFirst), outerLeft);
            } catch (const ElaborateError&) {
                // Outer expected type isn't an Equality — proceed
                // without synthesizing.
            }
        }
        ExpressionPointer firstEqualityKernel =
            elaborateExpression(*firstEqualitySurface, localBinders,
                                  expectedForFirst);
        ExpressionPointer firstEqualityType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          firstEqualityKernel));
        EqualityComponents firstComponents = extractEqualityComponents(
            firstEqualityType,
            "Equality.transitivity (first argument)", line);
        // Build the closed-over endpoints early so we can compose a
        // synthetic expected type for the second argument.
        ExpressionPointer carrierTypeForExpected =
            closeOverLocalBinders(firstComponents.carrierType,
                                    localBinders, localBinders.size());
        ExpressionPointer middleForExpected =
            closeOverLocalBinders(firstComponents.rightEndpoint,
                                    localBinders, localBinders.size());
        ExpressionPointer expectedForSecond = makeConstant(
            "Equality",
            {firstComponents.carrierUniverseLevel});
        expectedForSecond = makeApplication(
            std::move(expectedForSecond), carrierTypeForExpected);
        expectedForSecond = makeApplication(
            std::move(expectedForSecond), middleForExpected);
        expectedForSecond = makeApplication(
            std::move(expectedForSecond), middleForExpected);
        ExpressionPointer secondEqualityKernel =
            elaborateExpression(*secondEqualitySurface, localBinders,
                                  expectedForSecond);
        ExpressionPointer secondEqualityType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          secondEqualityKernel));
        EqualityComponents secondComponents = extractEqualityComponents(
            secondEqualityType,
            "Equality.transitivity (second argument)", line);
        ExpressionPointer carrierType = closeOverLocalBinders(
            firstComponents.carrierType,
            localBinders, localBinders.size());
        ExpressionPointer leftEndpoint = closeOverLocalBinders(
            firstComponents.leftEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer middleEndpoint = closeOverLocalBinders(
            firstComponents.rightEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer rightEndpoint = closeOverLocalBinders(
            secondComponents.rightEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer call = makeConstant(
            "Equality.transitivity",
            {firstComponents.carrierUniverseLevel});
        call = makeApplication(std::move(call), std::move(carrierType));
        call = makeApplication(std::move(call), std::move(leftEndpoint));
        call = makeApplication(std::move(call),
                                std::move(middleEndpoint));
        call = makeApplication(std::move(call), std::move(rightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(firstEqualityKernel));
        call = makeApplication(std::move(call),
                                std::move(secondEqualityKernel));
        (void)column;
        return call;
    }


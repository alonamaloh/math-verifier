// Out-of-line Elaborator method definitions: arithmetic-operator desugaring + reflexivity/symmetry/transitivity desugaring + extractEqualityComponents
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

#include <iostream>

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
        // `--check-redundant-casts`: an operand written as an explicit
        // ascription `(e : T)` is noise if the coercion-join would lift the
        // bare `e` to the same term. Elaborate the operator for real (guarded,
        // so the recursion runs the normal path), then re-elaborate it with
        // each operand's ascription stripped; a STRUCTURALLY identical result
        // means the cast is redundant. Structural (not defeq) equality keeps
        // us from flagging a cast whose removal would change the term's atom
        // association (which `ring`/hypothesis-matching can be sensitive to).
        // Suppressed inside a calc (`calcDepth_`). Residual false positives are
        // possible where a single source cast is consumed BOTH as an operator
        // operand (join lifts it) and as a carrier-typed term elsewhere (a bare
        // calc statement's last endpoint, which the join does not reach) — so
        // this is a candidate generator: verify a removal by rebuilding.
        if (reportRedundantCasts_ && !inRedundantCastProbe_ && calcDepth_ == 0
            && (std::holds_alternative<SurfaceAscription>(leftSurface.node)
                || std::holds_alternative<SurfaceAscription>(
                       rightSurface.node))) {
            inRedundantCastProbe_ = true;
            struct ProbeGuard {
                bool& flag;
                ~ProbeGuard() { flag = false; }
            } probeGuard{inRedundantCastProbe_};
            ExpressionPointer realResult = desugarArithmeticOperator(
                operatorSymbol, leftSurface, rightSurface, localBinders,
                expectedType, line);
            auto probe = [&](bool probeLeft) {
                const SurfaceExpression& operand =
                    probeLeft ? leftSurface : rightSurface;
                auto* ascription =
                    std::get_if<SurfaceAscription>(&operand.node);
                if (!ascription) return;
                ExpressionPointer stripped;
                try {
                    stripped = probeLeft
                        ? desugarArithmeticOperator(
                              operatorSymbol, *ascription->expression,
                              rightSurface, localBinders, expectedType, line)
                        : desugarArithmeticOperator(
                              operatorSymbol, leftSurface,
                              *ascription->expression, localBinders,
                              expectedType, line);
                } catch (const ElaborateError&) { return; }
                  catch (const TypeError&) { return; }
                if (stripped && structurallyEqual(stripped, realResult)) {
                    std::cerr << "warning: " << moduleName_ << ":"
                        << operand.line << ":" << operand.column
                        << ": redundant cast — the `" << operatorSymbol
                        << "` coercion-join already lifts this operand; "
                        "drop the `( : …)`\n";
                }
            };
            probe(true);
            probe(false);
            return realResult;
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
        // The LEFT operand is elaborated WITHOUT any expected type: a data
        // operator's operand types are synthesized bottom-up, so the
        // operator (`+`, `*`, `≤`, …) is selected from the operands' own
        // types and NEVER from an enclosing context. In particular an outer
        // cast like `(expr + 1 : Integer)` does not push `Integer` into
        // `expr` — it elaborates `expr + 1` in its own type and coerces the
        // *result*. This keeps a data expression's type independent of
        // context. (The left operand's actual type is still propagated to
        // the RIGHT operand below, since the operator is homogeneous.)
        ExpressionPointer leftKernel =
            elaborateExpression(leftSurface, localBinders);
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
        // right operand. This lets short-form `Quotient.class_of(rep)` (with
        // R inferred from expected type) fire in operand position of
        // homogeneous operators like `+`, `*`, `≤`, `<` on Rational,
        // Real, etc. — mirrors the `=` desugaring's identical trick.
        // The propagation is a HINT, not a requirement: a heterogeneous
        // operator's right operand lives at a different carrier (the
        // vector of `a • v`), and pushing the scalar's type into it can
        // poison its own implicit inference (e.g. the `{A}` of a
        // `Subtype.value(x)` operand). The poisoned term may only fail
        // at type inference, so checked-mode elaboration and the type
        // inference of its result share one retry: if either fails,
        // re-elaborate bottom-up — the registry lookup below dispatches
        // on the operand's own type either way.
        ExpressionPointer leftTypeClosed = closeOverLocalBinders(
            leftTypeRaw, localBinders, localBinders.size());
        ExpressionPointer rightKernel;
        ExpressionPointer rightTypeRaw;
        auto elaborateRightBottomUp = [&]() {
            rightKernel = elaborateExpression(rightSurface, localBinders);
            rightTypeRaw = inferTypeInLocalContext(localBinders, rightKernel);
        };
        try {
            rightKernel = elaborateExpression(rightSurface, localBinders,
                                              leftTypeClosed);
            rightTypeRaw = inferTypeInLocalContext(localBinders, rightKernel);
        } catch (const ElaborateError&) {
            elaborateRightBottomUp();
        } catch (const TypeError&) {
            elaborateRightBottomUp();
        }
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
        std::string rightTypeName = headConstantName(rightTypeRaw);
        // Heterogeneous operators register at an exact (left, right) pair
        // whose sides are DIFFERENT carriers — `^` : base^exponent is
        // `(Real, Natural)`, base and exponent at unrelated types. Consult
        // the registry on the RAW operand types before the coercion-join
        // below rewrites them: that join assumes a homogeneous operator and
        // would lift the exponent up to the base's carrier, hiding the exact
        // heterogeneous registration (and looking up a homogeneous pair that
        // does not exist). A homogeneous mismatch like `Rational + Real` has
        // no raw `(Rational, Real)` registration, so this misses and the
        // join still fires — no regression.
        {
            std::string rawHit = environment_.lookupOperator(
                operatorSymbol, operandTypeName, rightTypeName);
            if (!rawHit.empty()) targetFunction = rawHit;
        }
        // Mixed operands: reconcile via the coercion order before the
        // registry lookup. When a join exists (e.g. `Rational + Real`),
        // lift the lower operand up to it so the rest of this function
        // sees a homogeneous pair at the join type — registry dispatch,
        // implicit-filler inference, and the Natural `<` special case all
        // then operate on the coerced operands. See PLAN_COERCIONS.md.
        if (targetFunction.empty() && operandTypeName != rightTypeName) {
            ExpressionPointer rightTypeClosed = closeOverLocalBinders(
                rightTypeRaw, localBinders, localBinders.size());
            if (auto combined = combineOperands(
                    operandTypeName, rightTypeName,
                    leftTypeClosed, rightTypeClosed)) {
                // Cast-normal form at elaboration (PLAN_CAST_NORMALIZATION.md,
                // Option B): when the join coerces a *compound* operand it
                // would produce `ι(a ⊕ b)`; push the coercion to the leaves
                // now (`ι(a) ⊕ ι(b)`) so every downstream consumer sees one
                // canonical form. A no-op on a coerced leaf (`ι(q)`).
                leftKernel = applyCoercionChain(
                    std::move(leftKernel), combined->coerceLeft);
                if (!combined->coerceLeft.empty()) {
                    leftKernel =
                        castPushToLeaves(leftKernel, localBinders).term;
                }
                rightKernel = applyCoercionChain(
                    std::move(rightKernel), combined->coerceRight);
                if (!combined->coerceRight.empty()) {
                    rightKernel =
                        castPushToLeaves(rightKernel, localBinders).term;
                }
                leftTypeRaw = combined->resultType;
                leftTypeClosed = combined->resultType;
                rightTypeRaw = combined->resultType;
                operandTypeName = headConstantName(combined->resultType);
                rightTypeName = operandTypeName;
            }
        }
        std::string registered = environment_.lookupOperator(
            operatorSymbol, operandTypeName, rightTypeName);
        if (!registered.empty()) {
            targetFunction = registered;
        }
        // Fallback: if the raw head Constant didn't match anything,
        // try operand-type names from the registry whose definition
        // δ-reduces to the operand's actual type. This catches
        // `Quotient.class_of(IntegerRepresentative, IntegerEquivalent, _)`
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
                // `∣` is registered like `+`/`*` via the operator registry —
                // `operator (∣) on (Natural, Natural) := Natural.divides`
                // (Natural/divisibility) and `(Ring.carrier, Ring.carrier)` for
                // the ring form — so no built-in special case is needed here.
            }
        }
        // Expected-type fallback: the operands' own types resolve no
        // operator, but the ambient expected type E has a homogeneous
        // registration (op, E, E) and BOTH operands coerce into E — lift
        // them and dispatch at E. This is what lets `1 / 2` and `1 / k!`
        // elaborate as REAL division in a Real-typed position: the
        // operands are naturals, nothing below the fields divides, and
        // the surrounding type is the mathematician's intent. Purely
        // additive — this point is reached only where elaboration
        // previously errored, so no existing dispatch changes.
        if (targetFunction.empty() && expectedType) {
            std::string expectedName = headConstantName(expectedType);
            if (!expectedName.empty() && expectedName != operandTypeName) {
                std::string registeredAtExpected = environment_.lookupOperator(
                    operatorSymbol, expectedName, expectedName);
                auto chainTo = [&](const std::string& from)
                        -> std::optional<std::vector<std::string>> {
                    if (from == expectedName) {
                        return std::vector<std::string>{};
                    }
                    auto it = environment_.coercionRegistry.find(
                        std::make_tuple(from, expectedName));
                    if (it != environment_.coercionRegistry.end()) {
                        return it->second;
                    }
                    return std::nullopt;
                };
                auto leftChain = chainTo(operandTypeName);
                auto rightChain = chainTo(rightTypeName);
                if (!registeredAtExpected.empty() && leftChain && rightChain) {
                    leftKernel = applyCoercionChain(
                        std::move(leftKernel), *leftChain);
                    if (!leftChain->empty()) {
                        leftKernel =
                            castPushToLeaves(leftKernel, localBinders).term;
                    }
                    rightKernel = applyCoercionChain(
                        std::move(rightKernel), *rightChain);
                    if (!rightChain->empty()) {
                        rightKernel =
                            castPushToLeaves(rightKernel, localBinders).term;
                    }
                    leftTypeClosed = expectedType;
                    operandTypeName = expectedName;
                    rightTypeName = expectedName;
                    targetFunction = registeredAtExpected;
                }
            }
        }
        if (targetFunction.empty()) {
            throw ElaborateError(
                "operator '" + operatorSymbol + "' is not supported for "
                "operand type '" + operandTypeName
                + "'; supported: +, *, ≤, <, ∣ on Natural; +, *, - on "
                "Integer; ∧, ∨ on Proposition",
                line, 0);
        }
        if (environment_.lookup(targetFunction) == nullptr) {
            std::string message =
                "operator '" + operatorSymbol + "' at operand type '"
                + operandTypeName + "' resolves to '" + targetFunction
                + "' but that function is not in scope";
            if (wrapLeftInSuccessor) {
                // The baffling special case: `<` at Natural is
                // implemented as `successor(a) ≤ b`, so the missing
                // function is the ≤ it desugars to. Say so — and flag
                // the usual real cause, a numeral left operand typed
                // bottom-up as Natural beside a wider right operand.
                message +=
                    "\n  (`a < b` at Natural desugars to `successor(a) ≤ b`,"
                    " so `<` needs Natural's `≤` — import Natural.order)."
                    "\n  If the other operand is a wider type (Integer/"
                    "Rational/Real), the mismatch usually means a bare"
                    " numeral on the LEFT was typed as Natural: ascribe it"
                    " (`(0 : Real) < x`) or flip the comparison"
                    " (`x > 0`).";
            }
            throw ElaborateError(message, line, 0);
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
        ExpressionPointer call = applyOperatorImplicitFillers(
            makeConstant(targetFunction), targetFunction, leftTypeClosed,
            closeOverLocalBinders(rightTypeRaw, localBinders,
                                  localBinders.size()));
        call = makeApplication(std::move(call), std::move(leftKernel));
        call = makeApplication(std::move(call), std::move(rightKernel));
        // Discharge any trailing propositional side-condition the operator
        // function still expects after its two operands — e.g. the `d ≠ 0`
        // argument behind `/`. This is what lets `/` omit the nonzero witness.
        return dischargeTrailingSideConditions(
            std::move(call), localBinders, operatorSymbol, line);
    }

ExpressionPointer Elaborator::applyOperatorImplicitFillers(
        ExpressionPointer call, const std::string& targetFunction,
        ExpressionPointer leftTypeClosed,
        ExpressionPointer rightTypeClosed) {
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
        // alias like `Real = Quotient(_, _)`. Shared by the operator
        // desugaring, the calc relation-head builder, and the calc
        // relation-composition fold (whose transitivity lemmas — e.g.
        // `Set.subset.transitive {T}` — carry the same leading-implicit
        // shape, with the first explicit argument at the operand type).
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
                        // A structural match that binds only SOME implicits
                        // is kept: a heterogeneous operator's left type may
                        // not mention them all (`VectorSpace.scale {f} {V} :
                        // Field.carrier(f) → VectorSpace.carrier(V) → …`
                        // behind `•` pins only {f} from the scalar) — the
                        // right-operand phase below fills the rest.
                        std::vector<ExpressionPointer> partialBindings;
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
                                if (!inferredByUnification
                                    && partialBindings.empty()) {
                                    partialBindings = implicitBindings;
                                }
                            }
                            if (inferredByUnification) break;
                            ExpressionPointer next =
                                unfoldHeadConstantOneStep(leftCandidate);
                            if (!next) break;
                            leftCandidate = next;
                        }
                        if (!inferredByUnification) {
                            std::fill(implicitBindings.begin(),
                                      implicitBindings.end(), nullptr);
                            if (!partialBindings.empty()) {
                                implicitBindings = partialBindings;
                            }
                        }
                        // Right-operand phase: recover the implicits the
                        // left type left open from the RIGHT operand's type
                        // against the SECOND explicit domain (whose pattern
                        // additionally binds the first explicit binder —
                        // one extra metavariable slot, unused).
                        if (!inferredByUnification && rightTypeClosed) {
                            auto* secondExplicit = std::get_if<Pi>(
                                &firstExplicit->codomain->node);
                            if (secondExplicit) {
                                std::vector<ExpressionPointer>
                                    rightBindings(implicitCount + 1);
                                bool rightMatched = false;
                                ExpressionPointer rightCandidate =
                                    rightTypeClosed;
                                for (int step = 0;
                                     step < 64 && !rightMatched; ++step) {
                                    std::fill(rightBindings.begin(),
                                              rightBindings.end(), nullptr);
                                    rightMatched = matchAgainstPattern(
                                        secondExplicit->domain,
                                        rightCandidate,
                                        implicitCount + 1, rightBindings);
                                    if (rightMatched) break;
                                    ExpressionPointer next =
                                        unfoldHeadConstantOneStep(
                                            rightCandidate);
                                    if (!next) break;
                                    rightCandidate = next;
                                }
                                if (rightMatched) {
                                    inferredByUnification = true;
                                    for (int i = 0; i < implicitCount;
                                         ++i) {
                                        ExpressionPointer fromRight =
                                            rightBindings[i + 1];
                                        if (!implicitBindings[i]) {
                                            implicitBindings[i] = fromRight;
                                        } else if (fromRight
                                                   && !structurallyEqual(
                                                          implicitBindings[i],
                                                          fromRight)) {
                                            // The two operands disagree —
                                            // fall back to the heuristic
                                            // (the kernel typecheck will
                                            // report honestly).
                                            inferredByUnification = false;
                                            break;
                                        }
                                        if (!implicitBindings[i]) {
                                            inferredByUnification = false;
                                            break;
                                        }
                                    }
                                }
                            }
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
        return call;
    }

ExpressionPointer Elaborator::tryProvePositive(
        ExpressionPointer value, ExpressionPointer zeroTerm,
        const std::string& typeName,
        const std::vector<LocalBinder>& localBinders, int line) {
        // Inspect the raw form (NOT WHNF): the coercions are plain definitions,
        // so weak-head-normalising would unfold them and hide the cast head.
        // Peel a coercion `to_<Target>(inner)` (off both value and zeroTerm) and
        // apply the matching per-hop positive_preserves rung.
        auto* valueApp = std::get_if<Application>(&value->node);
        auto* zeroApp = std::get_if<Application>(&zeroTerm->node);
        if (valueApp && zeroApp) {
            auto* castConstant =
                std::get_if<Constant>(&valueApp->function->node);
            auto* zeroCastConstant =
                std::get_if<Constant>(&zeroApp->function->node);
            if (castConstant && zeroCastConstant
                && castConstant->name == zeroCastConstant->name) {
                std::string lemma;
                std::string innerType;
                if (castConstant->name == "Rational.to_real") {
                    lemma = "Rational.to_real.positive_preserves";
                    innerType = "Rational";
                } else if (castConstant->name == "Integer.to_rational") {
                    lemma = "Integer.to_rational.positive_preserves";
                    innerType = "Integer";
                } else if (castConstant->name == "Natural.to_integer") {
                    lemma = "Natural.to_integer.positive_preserves";
                    innerType = "Natural";
                }
                if (!lemma.empty() && environment_.lookup(lemma)) {
                    ExpressionPointer inner = valueApp->argument;
                    ExpressionPointer innerZero = zeroApp->argument;
                    ExpressionPointer innerProof = tryProvePositive(
                        inner, innerZero, innerType, localBinders, line);
                    if (!innerProof) return nullptr;
                    ExpressionPointer proof = makeConstant(lemma, {});
                    proof = makeApplication(proof, inner);
                    proof = makeApplication(proof, innerProof);
                    return proof;
                }
            }
        }
        // Base: hand `zeroTerm < value` to the auto-prover (shallow now — one
        // level of positivity, using the goal's own well-formed zero). `value`
        // and `zeroTerm` are CLOSED, so the goal is already in the form
        // autoProveClaim expects.
        if (!environment_.lookup(typeName + ".LessThan")) return nullptr;
        ExpressionPointer goalClosed = makeApplication(
            makeApplication(makeConstant(typeName + ".LessThan", {}), zeroTerm),
            value);
        // The general prover first.
        try {
            ExpressionPointer r = autoProveClaim(goalClosed, localBinders, line);
            if (r) return r;
        } catch (const ElaborateError&) {
        } catch (const TypeError&) {
        } catch (const AutoProverBudgetError&) {
        }
        // Natural base: `0 < value` = `zero_lt_of_one_le(value, «1 ≤ value»)`.
        // The `1 ≤ value` premise IS auto-provable (e.g. `less_or_equal_add_right`
        // for `1 + k`); constructing the application directly avoids relying on
        // the automatic path reaching `0 < _` through the opaque `<`.
        if (typeName == "Natural"
            && environment_.lookup("Natural.zero_lt_of_one_le")) {
            ExpressionPointer natOne = makeApplication(
                makeConstant("successor", {}), makeConstant("zero", {}));
            ExpressionPointer oneLeClosed = makeApplication(
                makeApplication(makeConstant("Natural.LessOrEqual", {}), natOne),
                value);
            ExpressionPointer oneLeProof = nullptr;
            try {
                oneLeProof = autoProveClaim(oneLeClosed, localBinders, line);
            } catch (const ElaborateError&) {
                oneLeProof = nullptr;
            } catch (const TypeError&) {
                oneLeProof = nullptr;
            } catch (const AutoProverBudgetError&) {
                oneLeProof = nullptr;
            }
            if (oneLeProof) {
                ExpressionPointer p =
                    makeConstant("Natural.zero_lt_of_one_le", {});
                p = makeApplication(p, value);
                p = makeApplication(p, oneLeProof);
                return p;
            }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryProveNonzero(
        ExpressionPointer obligationClosed,
        const std::vector<LocalBinder>& localBinders, int line) {
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer goalOpened =
            openOverLocalBinders(obligationClosed, localBinders, N);
        ExpressionPointer goalWhnf =
            weakHeadNormalForm(environment_, goalOpened);
        auto* notPi = std::get_if<Pi>(&goalWhnf->node);
        if (!notPi || referencesBoundVariable(notPi->codomain, 0)) {
            return nullptr;
        }
        ExpressionPointer codomainWhnf = weakHeadNormalForm(
            environment_, shift(notPi->codomain, -1));
        auto* codomainConstant = std::get_if<Constant>(&codomainWhnf->node);
        if (!codomainConstant || codomainConstant->name != "False") {
            return nullptr;
        }
        EqualityComponents equality;
        try {
            equality = extractEqualityComponents(
                notPi->domain, "nonzero tactic", line);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
        std::string typeName = headConstantName(equality.carrierType);
        if (typeName.empty()) return nullptr;
        std::string nonzeroLemma = typeName + ".nonzero_of_positive";
        if (!environment_.lookup(nonzeroLemma)) return nullptr;
        // The endpoints were extracted from the OPENED goal (kernel-operation
        // form); the proof must be CLOSED — that is what autoProveClaim's base
        // results are and what the discharge site applies onto `call`. Close
        // them here so the whole proof is assembled in one convention.
        ExpressionPointer valueClosed = closeOverLocalBinders(
            equality.leftEndpoint, localBinders, N);
        ExpressionPointer zeroClosed = closeOverLocalBinders(
            equality.rightEndpoint, localBinders, N);
        ExpressionPointer positivity = tryProvePositive(
            valueClosed, zeroClosed, typeName, localBinders, line);
        if (!positivity) return nullptr;
        // `<T>.nonzero_of_positive(b, positivity) : b ≠ T.zero` — the kernel
        // checks this against the obligation `b ≠ <the goal's zero>` up to defeq.
        ExpressionPointer proof = makeConstant(nonzeroLemma, {});
        proof = makeApplication(proof, valueClosed);
        proof = makeApplication(proof, positivity);
        return proof;
    }

ExpressionPointer Elaborator::dischargeTrailingSideConditions(
        ExpressionPointer call,
        const std::vector<LocalBinder>& localBinders,
        const std::string& operatorSymbol,
        int line) {
        for (int discharged = 0; discharged < 8; ++discharged) {
            ExpressionPointer callType =
                inferTypeInLocalContext(localBinders, call);
            ExpressionPointer callTypeWhnf =
                weakHeadNormalForm(environment_, callType);
            auto* pi = std::get_if<Pi>(&callTypeWhnf->node);
            if (!pi) break;
            Context obligationContext =
                buildContextFromLocalBinders(localBinders);
            if (!typeIsProposition(obligationContext, pi->domain)) break;
            ExpressionPointer obligationClosed = closeOverLocalBinders(
                pi->domain, localBinders, localBinders.size());
            // The general auto-prover first — its proof is what existing sites
            // (and lemmas that bake in the nonzero witness via `Logic.the`)
            // expect, so it must stay authoritative wherever it succeeds. Only
            // when it can't discharge (e.g. a cast denominator, defeated by the
            // backward-chain depth cap) do we fall back to the dedicated
            // structural `≠ 0` prover.
            ExpressionPointer proof = nullptr;
            int savedAutoProveDepth = autoProveDepth_;
            int savedBackwardChainingDepth = backwardChainingDepth_;
            try {
                proof = autoProveClaim(obligationClosed, localBinders, line);
            } catch (const AutoProverBudgetError&) {
                proof = nullptr;
            } catch (const ElaborateError&) {
                proof = nullptr;
            } catch (const TypeError&) {
                proof = nullptr;
            }
            if (!proof) {
                // A caught failure above may have left the prover's depth
                // counters unbalanced; restore them so the structural fallback
                // runs from a clean state.
                autoProveDepth_ = savedAutoProveDepth;
                backwardChainingDepth_ = savedBackwardChainingDepth;
                proof = tryProveNonzero(obligationClosed, localBinders, line);
            }
            if (!proof) {
                throwElaborate(
                    "operator '" + operatorSymbol + "' leaves the side "
                    "condition `"
                    + prettyPrintInLocalScope(obligationClosed, localBinders)
                    + "` to be discharged, but the auto-prover could not "
                    "establish it here — provide the needed hypothesis "
                    "(e.g. that the denominator is nonzero) in scope");
            }
            call = makeApplication(std::move(call), std::move(proof));
        }
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
        auto failNotEquality = [&]() -> ElaborateError {
            return ElaborateError(
                std::string(contextLabel)
                + ": the goal is not an equality — its type is `"
                + prettyPrintForDisplay(equalityType)
                + "` (line " + std::to_string(line) + "). "
                + (std::string(contextLabel) == "ring"
                       ? "`ring` proves `=` goals only; for an order or "
                         "other relation goal, put the ring step inside a "
                         "calc chain whose steps carry the relation."
                       : "Expected a fully applied `Equality(T, a, b)`."));
        };
        auto* outerApp = std::get_if<Application>(&equalityType->node);
        if (!outerApp) {
            throw failNotEquality();
        }
        ExpressionPointer rightEndpoint = outerApp->argument;
        auto* middleApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!middleApp) {
            throw failNotEquality();
        }
        ExpressionPointer leftEndpoint = middleApp->argument;
        auto* innerApp =
            std::get_if<Application>(&middleApp->function->node);
        if (!innerApp) {
            throw failNotEquality();
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


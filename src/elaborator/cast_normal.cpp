// Out-of-line Elaborator method definitions: cast normalization.
//
// Part of the elaborator split (see internal.hpp). This translation unit
// holds `castPushToLeaves` — the reusable core that drives coercions over
// compound subterms down to the leaves, so that the coercion-join's
// association-sensitive output (`ι(1 + n)` from `1 + n + x`) is reconciled
// with the leaf-cast form (`ι(1) + ι(n)`). See PLAN_CAST_NORMALIZATION.md.
//
// The transform is gated by the registered `<coercion>.<op>_preserves`
// homomorphism lemmas: it pushes a cast through an operation only where the
// corresponding move lemma exists. This makes it sound by construction —
// Natural subtraction is monus, has no `subtract_preserves`, and so is
// never distributed (`ι(a - b) ≠ ι(a) - ι(b)` there).

#include "elaborator/internal.hpp"

namespace {

// Diagnostic telemetry (`MATH_CAST_TIER_DEBUG=1`): one stderr line per
// tryCastEqualityTier invocation recording the outcome, so the yield of
// prospective B3.x extensions can be sized from a classifier run instead
// of guessed. Not a user-facing feature; costs nothing when unset.
bool castTierDebugEnabled() {
    static const bool enabled = [] {
        const char* flag = std::getenv("MATH_CAST_TIER_DEBUG");
        return flag && flag[0] != '\0' && flag[0] != '0';
    }();
    return enabled;
}

// A binary ring operation `<carrier>.<suffix>(a, b)` on a CONCRETE carrier
// (exactly two explicit arguments, constant head). Bundled/abstract
// carriers carry a leading structure argument and so do not match — which
// is correct, since coercions exist only between the concrete numeric
// types. `suffix` is one of "add" / "multiply" / "subtract".
struct BinaryOp {
    std::string opName;   // e.g. "Rational.add"
    std::string suffix;   // e.g. "add"
    ExpressionPointer left;
    ExpressionPointer right;
};

std::optional<BinaryOp> asBinaryOp(ExpressionPointer term) {
    auto* outer = std::get_if<Application>(&term->node);
    if (!outer) return std::nullopt;
    auto* inner = std::get_if<Application>(&outer->function->node);
    if (!inner) return std::nullopt;
    auto* head = std::get_if<Constant>(&inner->function->node);
    if (!head) return std::nullopt;
    // `divide` earns its slot for the generic-descent side only: no
    // carrier pair has a `divide_preserves` move lemma (ℕ and ℤ have no
    // division), so a cast never distributes over it — but descending
    // INTO a quotient's operands is what lets the analysis files'
    // `ι(a)/ι(b!)` spellings normalize underneath.
    static const std::array<const char*, 4> suffixes{
        "add", "multiply", "subtract", "divide"};
    for (const char* suffix : suffixes) {
        std::string dotted = std::string(".") + suffix;
        const std::string& name = head->name;
        if (name.size() > dotted.size()
            && name.compare(name.size() - dotted.size(),
                            dotted.size(), dotted) == 0) {
            return BinaryOp{name, suffix, inner->argument, outer->argument};
        }
    }
    return std::nullopt;
}

}  // namespace

// Is `name` a registered coercion function (a primitive hop in some
// coercion chain)? The registry is tiny, so a linear scan is free.
bool Elaborator::isCoercionFunctionName(const std::string& name) const {
    for (const auto& [key, chain] : environment_.coercionRegistry) {
        (void)key;
        for (const auto& hop : chain) {
            if (hop == name) return true;
        }
    }
    return false;
}

// The norm_cast registry: every nullary library theorem `L = R` with a
// coercion image on one side (`ι(<T>.zero) = <carrier>.zero`, the shape of
// `from_real_zero`/`from_real_one`). Derived on demand from the declaration
// table — no new persisted state — and cached until the table grows (an
// O(1) `.size()` guard, so the steady state re-scan is free). The linter's
// numeral spellings (`(0 : ℂ)` ≡ `from_real(Real.zero)`) meet the ring
// quotient's own zero across these bridges.
const std::vector<Elaborator::NormalizationEquality>&
Elaborator::normalizationEqualities() {
    if (normalizationEqualitiesBuiltAtDeclCount_
            == environment_.declarations.size()) {
        return normalizationEqualitiesCache_;
    }
    normalizationEqualitiesCache_.clear();
    for (const auto& [name, declaration] : environment_.declarations) {
        const auto* definition = std::get_if<Definition>(&declaration);
        if (!definition || !definition->type) continue;
        // Ground only: a quantified homomorphism law (`from_real_add`) is
        // not a normalization equality between fixed spellings of a value.
        if (countLeadingPis(definition->type) != 0) continue;
        EqualityComponents components;
        try {
            components = extractEqualityComponents(
                definition->type, "normalization-equality scan", 0);
        } catch (const ElaborateError&) {
            continue;
        } catch (const TypeError&) {
            continue;
        }
        // One side must be a coercion image — this is what makes it a
        // norm_cast bridge, not an arbitrary ground equality.
        if (!isCoercionFunctionName(
                headConstantName(components.leftEndpoint))
            && !isCoercionFunctionName(
                headConstantName(components.rightEndpoint))) {
            continue;
        }
        if (containsFreeVariable(components.leftEndpoint)
            || containsFreeVariable(components.rightEndpoint)) {
            continue;
        }
        normalizationEqualitiesCache_.push_back(
            {components.leftEndpoint, components.rightEndpoint,
             components.carrierType, components.carrierUniverseLevel, name});
    }
    normalizationEqualitiesBuiltAtDeclCount_ =
        environment_.declarations.size();
    return normalizationEqualitiesCache_;
}

// Mechanism (4) of the citation-discharge fallback. The cited hint proves an
// equality that IS the goal once a registered normalization equality `L = R`
// is applied (`conj((0:ℂ)) = (0:ℂ)` proves `conj(RingModulo.zero) =
// RingModulo.zero` across `from_real(Real.zero) = RingModulo.zero`). Rewrite
// the goal `R ↦ L` — defeq-aware, so an occurrence hidden behind a reducible
// spelling (`partialSum(s, 0)` ≡ `RingModulo.zero`) is still found — close
// the rewrite with the hint, and transport back via
// `Equality.transport_proposition` (the same assembly `by substituting`
// uses). The caller validates the result defeq against the goal.
ExpressionPointer Elaborator::tryNormalizationEqualityBridge(
        const std::vector<LocalBinder>& localBinders,
        const ExpressionPointer& hintTerm,
        const ExpressionPointer& goalClosed,
        int line) {
    if (!hintTerm) return nullptr;
    const std::vector<NormalizationEquality>& registry =
        normalizationEqualities();
    if (registry.empty()) return nullptr;
    if (environment_.lookup("Equality.transport_proposition") == nullptr) {
        return nullptr;
    }
    // The hint's closed type — the fact we close each rewritten goal with.
    ExpressionPointer hintTypeClosed;
    try {
        hintTypeClosed = closeOverLocalBinders(
            inferTypeInLocalContext(localBinders, hintTerm),
            localBinders, localBinders.size());
    } catch (const ElaborateError&) {
        return nullptr;
    } catch (const TypeError&) {
        return nullptr;
    }
    Context openedContext = buildContextFromLocalBinders(localBinders);
    ExpressionPointer goalOpened =
        openOverLocalBinders(goalClosed, localBinders, localBinders.size());
    ExpressionPointer hintTypeOpened =
        openOverLocalBinders(hintTypeClosed, localBinders, localBinders.size());

    for (const NormalizationEquality& eq : registry) {
        int fromArity = 0;
        {
            ExpressionPointer head = eq.rhs;
            while (auto* app = std::get_if<Application>(&head->node)) {
                ++fromArity;
                head = app->function;
            }
        }
        for (int direction = 0; direction < 2; ++direction) {
            ExpressionPointer fromSide = (direction == 0) ? eq.rhs : eq.lhs;
            ExpressionPointer toSide = (direction == 0) ? eq.lhs : eq.rhs;
            int arity = fromArity;
            if (direction == 1) {
                arity = 0;
                ExpressionPointer head = eq.lhs;
                while (auto* app = std::get_if<Application>(&head->node)) {
                    ++arity;
                    head = app->function;
                }
            }
            // Abstract occurrences of `fromSide`: structural first (free),
            // then a bounded defeq pass so a reducible spelling is caught.
            int occurrences = 0;
            ExpressionPointer abstractedBody = abstractStructuralOccurrence(
                goalClosed, fromSide, /*currentDepth=*/0, occurrences);
            if (occurrences == 0) {
                int defeqBudget = 64;
                abstractedBody = abstractDefeqOccurrence(
                    goalClosed, fromSide, arity, /*currentDepth=*/0,
                    occurrences, defeqBudget);
            }
            if (occurrences == 0) continue;
            autoProveSpend(1);
            ExpressionPointer rewrittenGoal =
                substitute(abstractedBody, 0, toSide);
            // The rewrite must yield a well-typed goal.
            try {
                inferTypeInLocalContext(localBinders, rewrittenGoal);
            } catch (const ElaborateError&) {
                continue;
            } catch (const TypeError&) {
                continue;
            }
            // Close the rewritten goal with the hint: a direct defeq match
            // (the ground case — the hint's conclusion IS the rewrite up to
            // the numeral-tower defeq), else a bare-lemma-at-diff congruence
            // when the hint is quantified.
            ExpressionPointer rewrittenOpened = openOverLocalBinders(
                rewrittenGoal, localBinders, localBinders.size());
            ExpressionPointer proofRewritten;
            bool direct = false;
            try {
                direct = isDefinitionallyEqual(
                    environment_, openedContext, hintTypeOpened,
                    rewrittenOpened);
            } catch (const TypeError&) {
                direct = false;
            }
            if (direct) {
                proofRewritten = hintTerm;
            } else if (std::holds_alternative<Pi>(hintTypeClosed->node)) {
                try {
                    EqualityComponents rc = extractEqualityComponents(
                        weakHeadNormalForm(environment_, rewrittenOpened),
                        "normalization-bridge rewritten", line);
                    ExpressionPointer previous = closeOverLocalBinders(
                        rc.leftEndpoint, localBinders, localBinders.size());
                    ExpressionPointer next = closeOverLocalBinders(
                        rc.rightEndpoint, localBinders, localBinders.size());
                    proofRewritten = tryApplyBareLemmaToDiff(
                        localBinders, previous, next, hintTerm,
                        hintTypeClosed, line, 0);
                } catch (const ElaborateError&) {
                    proofRewritten = nullptr;
                } catch (const TypeError&) {
                    proofRewritten = nullptr;
                }
            }
            if (!proofRewritten) continue;
            // Transport back to the original goal. motive = λ hole. body;
            // transport_proposition(T, motive, a, b, (a=b), motive[a]) :
            // motive[b]. direction 0 rewrote R↦L, so motive[L] is the
            // rewritten goal (proofRewritten) and motive[R] the original.
            ExpressionPointer motive = makeLambda(
                "_normHole", eq.carrierType, abstractedBody);
            ExpressionPointer eqForTransport;
            ExpressionPointer transportLhs;
            ExpressionPointer transportRhs;
            if (direction == 0) {
                eqForTransport = makeConstant(eq.proofName);
                transportLhs = eq.lhs;
                transportRhs = eq.rhs;
            } else {
                eqForTransport = makeConstant(
                    "Equality.symmetry", {eq.carrierLevel});
                eqForTransport =
                    makeApplication(eqForTransport, eq.carrierType);
                eqForTransport = makeApplication(eqForTransport, eq.lhs);
                eqForTransport = makeApplication(eqForTransport, eq.rhs);
                eqForTransport = makeApplication(
                    eqForTransport, makeConstant(eq.proofName));
                transportLhs = eq.rhs;
                transportRhs = eq.lhs;
            }
            ExpressionPointer call = makeConstant(
                "Equality.transport_proposition", {eq.carrierLevel});
            call = makeApplication(call, eq.carrierType);
            call = makeApplication(call, motive);
            call = makeApplication(call, transportLhs);
            call = makeApplication(call, transportRhs);
            call = makeApplication(call, eqForTransport);
            call = makeApplication(call, proofRewritten);
            // Soundness guard: the assembled term must prove the goal.
            try {
                ExpressionPointer callType =
                    inferTypeInLocalContext(localBinders, call);
                if (isDefinitionallyEqual(
                        environment_, openedContext,
                        openOverLocalBinders(callType, localBinders,
                                             localBinders.size()),
                        goalOpened)) {
                    return call;
                }
            } catch (const ElaborateError&) {
            } catch (const TypeError&) {
            }
        }
    }
    return nullptr;
}

Elaborator::CastNormalForm Elaborator::castPushToLeaves(
        ExpressionPointer term,
        const std::vector<LocalBinder>& localBinders) {
    // Coercion application `ι(inner)`?
    if (auto* app = std::get_if<Application>(&term->node)) {
        if (auto* head = std::get_if<Constant>(&app->function->node)) {
            if (isCoercionFunctionName(head->name)) {
                return pushCoercion(head->name, app->argument, term,
                                    localBinders);
            }
        }
        // Generic descent through a concrete binary ring op at the target
        // carrier: normalize each operand, rebuild with a congruence proof.
        if (auto op = asBinaryOp(term)) {
            CastNormalForm leftNorm =
                castPushToLeaves(op->left, localBinders);
            CastNormalForm rightNorm =
                castPushToLeaves(op->right, localBinders);
            if (!leftNorm.proof && !rightNorm.proof) {
                return {term, nullptr};
            }
            ExpressionPointer carrier =
                inferTypeInLocalContext(localBinders, op->left);
            LevelPointer level = typeUniverseOf(localBinders, op->left);
            ExpressionPointer leftProof = leftNorm.proof
                ? leftNorm.proof
                : buildReflexivity(level, carrier, op->left);
            ExpressionPointer rightProof = rightNorm.proof
                ? rightNorm.proof
                : buildReflexivity(level, carrier, op->right);
            ExpressionPointer rebuilt = makeApplication(
                makeApplication(makeConstant(op->opName), leftNorm.term),
                rightNorm.term);
            ExpressionPointer proof = buildBinaryOpCongruence(
                op->opName, op->left, leftNorm.term, leftProof,
                op->right, rightNorm.term, rightProof, carrier, level);
            return {rebuilt, proof};
        }
    }
    // Atom (variable, literal, opaque application): nothing to push.
    return {term, nullptr};
}

// Normalize `ι(inner)` (`coercionName` is ι). Strategy: first normalize
// `inner`; then, if the normalized inner is `op(a, b)` and a move lemma
// `ι(op(a, b)) = op'(ι a, ι b)` is registered, rewrite to `op'(â, b̂)`
// (the recursively-normalized casts of the operands) and assemble the
// proof from the move lemma + congruences; otherwise leave `ι(inner')`.
Elaborator::CastNormalForm Elaborator::pushCoercion(
        const std::string& coercionName,
        ExpressionPointer inner,
        ExpressionPointer term,
        const std::vector<LocalBinder>& localBinders) {
    ExpressionPointer sourceCarrier =
        inferTypeInLocalContext(localBinders, inner);
    ExpressionPointer targetCarrier =
        inferTypeInLocalContext(localBinders, term);
    LevelPointer sourceLevel = typeUniverseOf(localBinders, inner);
    LevelPointer targetLevel = typeUniverseOf(localBinders, term);
    std::string targetCarrierName = headConstantName(targetCarrier);

    // Normalize underneath the coercion first, so a nested chain unwinds
    // innermost-out: `to_real(to_rational(to_integer(a+b)))` becomes a
    // Real sum once each layer is processed.
    CastNormalForm innerNorm = castPushToLeaves(inner, localBinders);
    auto coercionOf = [&](ExpressionPointer argument) {
        return makeApplication(makeConstant(coercionName),
                                std::move(argument));
    };
    // `ι(inner')`, and the proof `ι(inner) = ι(inner')` if inner moved.
    ExpressionPointer coercedInner = innerNorm.proof
        ? coercionOf(innerNorm.term)
        : term;
    ExpressionPointer innerCongruence = nullptr;
    if (innerNorm.proof) {
        ExpressionPointer lambda = makeLambda(
            "_cast_z", sourceCarrier,
            makeApplication(makeConstant(coercionName),
                             makeBoundVariable(0)));
        innerCongruence = buildEqualityCongruence(
            sourceLevel, sourceCarrier, targetLevel, targetCarrier,
            lambda, inner, innerNorm.term, innerNorm.proof);
    }

    // Can we distribute ι over the (normalized) inner operation?
    if (auto op = asBinaryOp(innerNorm.term)) {
        std::string lemmaName =
            coercionName + "." + op->suffix + "_preserves";
        if (environment_.lookup(lemmaName) != nullptr) {
            // proof0 : ι(op(a, b)) = op'(ι a, ι b)
            ExpressionPointer proof0 = makeApplication(
                makeApplication(makeConstant(lemmaName), op->left),
                op->right);
            std::string targetOpName =
                targetCarrierName + "." + op->suffix;
            ExpressionPointer coercedLeft = coercionOf(op->left);
            ExpressionPointer coercedRight = coercionOf(op->right);
            // Recurse into the freshly-exposed casts of the operands.
            CastNormalForm leftNorm =
                castPushToLeaves(coercedLeft, localBinders);
            CastNormalForm rightNorm =
                castPushToLeaves(coercedRight, localBinders);
            ExpressionPointer leftProof = leftNorm.proof
                ? leftNorm.proof
                : buildReflexivity(targetLevel, targetCarrier, coercedLeft);
            ExpressionPointer rightProof = rightNorm.proof
                ? rightNorm.proof
                : buildReflexivity(targetLevel, targetCarrier, coercedRight);
            ExpressionPointer distributed = makeApplication(
                makeApplication(makeConstant(targetOpName), coercedLeft),
                coercedRight);
            ExpressionPointer normalized = makeApplication(
                makeApplication(makeConstant(targetOpName), leftNorm.term),
                rightNorm.term);
            // op'(ι a, ι b) = op'(â, b̂)
            ExpressionPointer congruence = buildBinaryOpCongruence(
                targetOpName, coercedLeft, leftNorm.term, leftProof,
                coercedRight, rightNorm.term, rightProof,
                targetCarrier, targetLevel);
            // ι(inner') = op'(ι a, ι b) = op'(â, b̂)
            ExpressionPointer pushProof = buildEqualityTransitivity(
                targetLevel, targetCarrier, coercedInner, distributed,
                normalized, proof0, congruence);
            // Prepend ι(inner) = ι(inner') if inner itself moved.
            ExpressionPointer proof = innerCongruence
                ? buildEqualityTransitivity(
                      targetLevel, targetCarrier, term, coercedInner,
                      normalized, innerCongruence, pushProof)
                : pushProof;
            return {normalized, proof};
        }
    }
    // No distribution at this layer; the only change (if any) is inside.
    return {coercedInner, innerCongruence};
}

// B3.3a — the factoring dual of `castPushToLeaves`: try to express
// `term` (at the target carrier) as the image `ι(source)` of a single
// term at the hop's source carrier, collapsing leaf casts back through
// the registered `<hop>.<op>_preserves` lemmas run right-to-left.
// Succeeds only when EVERY leaf is reachable — a cast `ι(x)`, a
// carrier constant with a `zero`/`one` preservation lemma, or an
// add/multiply/subtract node whose operands both pull. A bare
// target-carrier atom anywhere fails the pull, which is correct: such
// a term has no preimage spelling. The payoff is compound LOWERING:
// `ι q · ι m + ι r  =  ι j` becomes `q · m + r = j` at the source
// carrier, where the context facts that close it actually live.
std::optional<Elaborator::PulledCast> Elaborator::castPullToRoot(
        ExpressionPointer term,
        const std::string& hopName,
        const std::string& sourceCarrierName,
        const std::string& targetCarrierName,
        ExpressionPointer targetCarrier,
        LevelPointer targetLevel,
        const std::vector<LocalBinder>& localBinders) {
    // Direct image `ι(source)`.
    if (auto* app = std::get_if<Application>(&term->node)) {
        if (auto* head = std::get_if<Constant>(&app->function->node)) {
            if (head->name == hopName) {
                return PulledCast{app->argument, nullptr};
            }
        }
    }
    auto coercionOf = [&](ExpressionPointer argument) {
        return makeApplication(makeConstant(hopName), std::move(argument));
    };
    // Carrier constant with a preservation lemma: `<T>.zero` / `<T>.one`
    // pulls to the literal the lemma `ι(lit) = <T>.zero/one` names.
    if (auto* constant = std::get_if<Constant>(&term->node)) {
        std::string suffix;
        if (constant->name == targetCarrierName + ".zero") suffix = "zero";
        if (constant->name == targetCarrierName + ".one") suffix = "one";
        if (!suffix.empty()) {
            std::string lemmaName = hopName + "." + suffix + "_preserves";
            const Declaration* declaration = environment_.lookup(lemmaName);
            if (auto* definition =
                    declaration ? std::get_if<Definition>(declaration)
                                : nullptr) {
                // Statement shape: Equality(T, ι(lit), <T>.zero/one).
                auto* eqApp =
                    std::get_if<Application>(&definition->type->node);
                auto* eqApp2 = eqApp
                    ? std::get_if<Application>(&eqApp->function->node)
                    : nullptr;
                if (eqApp && eqApp2) {
                    ExpressionPointer stated = eqApp->argument;
                    ExpressionPointer image = eqApp2->argument;
                    auto* imageApp =
                        std::get_if<Application>(&image->node);
                    auto* imageHead = imageApp
                        ? std::get_if<Constant>(&imageApp->function->node)
                        : nullptr;
                    if (imageHead && imageHead->name == hopName
                        && structurallyEqual(stated, term)) {
                        // lemma : ι(lit) = term; we need term = ι(lit).
                        ExpressionPointer proof = buildEqualitySymmetry(
                            targetLevel, targetCarrier, image, term,
                            makeConstant(lemmaName));
                        return PulledCast{imageApp->argument, proof};
                    }
                }
            }
            return std::nullopt;
        }
    }
    // Binary carrier operation whose move lemma exists: pull both
    // operands, rebuild at the source carrier, and stitch
    //   op'(A, B) = op'(ι a, ι b) = ι(op(a, b))
    // from the operand proofs and the preserves lemma reversed.
    if (auto op = asBinaryOp(term)) {
        if (op->opName != targetCarrierName + "." + op->suffix) {
            return std::nullopt;
        }
        std::string lemmaName = hopName + "." + op->suffix + "_preserves";
        if (environment_.lookup(lemmaName) == nullptr) return std::nullopt;
        auto leftPull = castPullToRoot(
            op->left, hopName, sourceCarrierName, targetCarrierName,
            targetCarrier, targetLevel, localBinders);
        if (!leftPull) return std::nullopt;
        auto rightPull = castPullToRoot(
            op->right, hopName, sourceCarrierName, targetCarrierName,
            targetCarrier, targetLevel, localBinders);
        if (!rightPull) return std::nullopt;
        ExpressionPointer coercedLeft = coercionOf(leftPull->source);
        ExpressionPointer coercedRight = coercionOf(rightPull->source);
        ExpressionPointer source = makeApplication(
            makeApplication(
                makeConstant(sourceCarrierName + "." + op->suffix),
                leftPull->source),
            rightPull->source);
        // preserves(a, b) : ι(op(a, b)) = op'(ι a, ι b), reversed.
        ExpressionPointer distributed = makeApplication(
            makeApplication(
                makeConstant(op->opName), coercedLeft), coercedRight);
        ExpressionPointer collapse = buildEqualitySymmetry(
            targetLevel, targetCarrier, coercionOf(source), distributed,
            makeApplication(
                makeApplication(makeConstant(lemmaName), leftPull->source),
                rightPull->source));
        if (!leftPull->proof && !rightPull->proof) {
            // term IS op'(ι a, ι b) already.
            return PulledCast{source, collapse};
        }
        ExpressionPointer leftProof = leftPull->proof
            ? leftPull->proof
            : buildReflexivity(targetLevel, targetCarrier, op->left);
        ExpressionPointer rightProof = rightPull->proof
            ? rightPull->proof
            : buildReflexivity(targetLevel, targetCarrier, op->right);
        ExpressionPointer congruence = buildBinaryOpCongruence(
            op->opName, op->left, coercedLeft, leftProof,
            op->right, coercedRight, rightProof,
            targetCarrier, targetLevel);
        ExpressionPointer proof = buildEqualityTransitivity(
            targetLevel, targetCarrier, term, distributed,
            coercionOf(source), congruence, collapse);
        return PulledCast{source, proof};
    }
    return std::nullopt;
}

// B3.1 — the cast-equality tier. Runs when the equality battery has
// declined a step `previous = next`. Normalize both endpoints to
// leaf-cast form (proof-carrying); then:
//   1. If both normal forms are the SAME single-hop cast — `ι(a)` and
//      `ι(b)` — LOWER the goal to `a = b` at the source carrier,
//      re-run the battery there, and lift the found proof back through
//      ι by congruence. This is the reflection direction the
//      push-to-leaves transform alone cannot provide: the battery's
//      indexes speak the source carrier's lemmas (`a = b` over
//      Integer), which the cast-bearing spelling hides.
//   2. Otherwise, if normalization moved either endpoint, retry the
//      battery once at the normalized endpoints and stitch the
//      normalization proofs around the found core.
// Terminates: lowering strictly shortens the coercion chain, and the
// retry is guarded on "normalization moved something" (normal forms
// are fixpoints of castPushToLeaves).
ExpressionPointer Elaborator::tryCastEqualityTier(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        ExpressionPointer stepEqualityType,
        int line, int column) {
    autoProveSpend(2);

    // B3.3a — compound lowering. Before spreading casts out, try the
    // opposite move: FACTOR each endpoint as the image `ι(s)` of a
    // single source-carrier term and lower the whole equality to
    // `sL = sR` there. This is where the context facts live — a goal
    // `ι q · ι m + ι r = ι j` is the image of `q·m + r = j`, whose
    // proof is a hypothesis at the source carrier that no amount of
    // target-carrier normalization can reach. The battery re-runs at
    // the source (its own cast tier handles multi-hop towers, which
    // terminate because the coercion graph is acyclic).
    {
        std::string carrierName = headConstantName(carrierType);
        for (const auto& [registryKey, chain]
                 : environment_.coercionRegistry) {
            if (chain.size() != 1) continue;
            if (std::get<1>(registryKey) != carrierName) continue;
            const std::string& hopName = chain[0];
            const std::string& sourceName = std::get<0>(registryKey);
            std::optional<PulledCast> leftPull;
            std::optional<PulledCast> rightPull;
            try {
                leftPull = castPullToRoot(
                    previousKernel, hopName, sourceName, carrierName,
                    carrierType, carrierLevel, localBinders);
                if (leftPull) {
                    rightPull = castPullToRoot(
                        nextKernel, hopName, sourceName, carrierName,
                        carrierType, carrierLevel, localBinders);
                }
            } catch (const ElaborateError&) {
            } catch (const TypeError&) {
            }
            if (!leftPull || !rightPull) continue;
            // Both endpoints are ι-images: lower, re-prove, lift.
            autoProveSpend(2);
            ExpressionPointer sourceCarrier;
            LevelPointer sourceLevel;
            ExpressionPointer loweredProof;
            try {
                sourceCarrier = inferTypeInLocalContext(
                    localBinders, leftPull->source);
                sourceLevel = typeUniverseOf(localBinders,
                                             leftPull->source);
                ExpressionPointer loweredGoal = makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Equality", {sourceLevel}),
                            sourceCarrier),
                        leftPull->source),
                    rightPull->source);
                loweredProof = autoProveCalcStep(
                    localBinders, leftPull->source, rightPull->source,
                    sourceCarrier, sourceLevel, loweredGoal,
                    line, column);
            } catch (const ElaborateError&) {
            } catch (const TypeError&) {
            }
            if (!loweredProof) {
                if (castTierDebugEnabled()) {
                    std::cerr << "[cast-tier]\t" << moduleName_ << ":"
                              << line << "\tpull-lowered-fail\thop="
                              << hopName << "\n";
                }
                continue;
            }
            if (castTierDebugEnabled()) {
                std::cerr << "[cast-tier]\t" << moduleName_ << ":"
                          << line << "\tpull-lowered-ok\thop="
                          << hopName << "\n";
            }
            ExpressionPointer hopLambda = makeLambda(
                "_cast_z", sourceCarrier,
                makeApplication(makeConstant(hopName),
                                makeBoundVariable(0)));
            ExpressionPointer lifted = buildEqualityCongruence(
                sourceLevel, sourceCarrier, carrierLevel, carrierType,
                hopLambda, leftPull->source, rightPull->source,
                loweredProof);
            // previous = ι(sL) = ι(sR) = next.
            ExpressionPointer coercedLeft = makeApplication(
                makeConstant(hopName), leftPull->source);
            ExpressionPointer total = lifted;
            if (leftPull->proof) {
                total = buildEqualityTransitivity(
                    carrierLevel, carrierType, previousKernel,
                    coercedLeft, makeApplication(
                        makeConstant(hopName), rightPull->source),
                    leftPull->proof, total);
            }
            if (rightPull->proof) {
                ExpressionPointer reversed = buildEqualitySymmetry(
                    carrierLevel, carrierType, nextKernel,
                    makeApplication(makeConstant(hopName),
                                    rightPull->source),
                    rightPull->proof);
                total = buildEqualityTransitivity(
                    carrierLevel, carrierType, previousKernel,
                    makeApplication(makeConstant(hopName),
                                    rightPull->source),
                    nextKernel, total, reversed);
            }
            return total;
        }
    }

    CastNormalForm leftNorm =
        castPushToLeaves(previousKernel, localBinders);
    CastNormalForm rightNorm = castPushToLeaves(nextKernel, localBinders);

    auto singleHop = [&](ExpressionPointer term)
            -> std::optional<std::pair<std::string, ExpressionPointer>> {
        auto* app = std::get_if<Application>(&term->node);
        if (!app) return std::nullopt;
        auto* head = std::get_if<Constant>(&app->function->node);
        if (!head || !isCoercionFunctionName(head->name)) {
            return std::nullopt;
        }
        return std::make_pair(head->name, app->argument);
    };
    // Assemble previous = next from the three pieces
    //   previous = leftNorm.term   (normalization, or refl)
    //   leftNorm.term = rightNorm.term   (the found core)
    //   rightNorm.term = next   (normalization reversed, or refl)
    auto stitch = [&](ExpressionPointer coreProof) {
        ExpressionPointer total = coreProof;
        if (leftNorm.proof) {
            total = buildEqualityTransitivity(
                carrierLevel, carrierType, previousKernel,
                leftNorm.term, rightNorm.term, leftNorm.proof, total);
        }
        if (rightNorm.proof) {
            ExpressionPointer reversed = buildEqualitySymmetry(
                carrierLevel, carrierType, nextKernel, rightNorm.term,
                rightNorm.proof);
            total = buildEqualityTransitivity(
                carrierLevel, carrierType, previousKernel,
                rightNorm.term, nextKernel, total, reversed);
        }
        return total;
    };

    auto debugLine = [&](const char* outcome) {
        if (!castTierDebugEnabled()) return;
        auto brief = [&](ExpressionPointer term) {
            std::string text;
            try {
                text = prettyPrintInLocalScope(term, localBinders);
            } catch (...) { text = "<print-failed>"; }
            if (text.size() > 110) text.resize(110);
            return text;
        };
        std::cerr << "[cast-tier]\t" << moduleName_ << ":" << line
                  << "\t" << outcome
                  << "\tmovedL=" << (leftNorm.proof ? 1 : 0)
                  << " movedR=" << (rightNorm.proof ? 1 : 0)
                  << "\tL=" << brief(leftNorm.term)
                  << "\tR=" << brief(rightNorm.term) << "\n";
    };

    auto leftHop = singleHop(leftNorm.term);
    auto rightHop = singleHop(rightNorm.term);
    if (leftHop && rightHop && leftHop->first == rightHop->first) {
        ExpressionPointer loweredLeft = leftHop->second;
        ExpressionPointer loweredRight = rightHop->second;
        ExpressionPointer sourceCarrier =
            inferTypeInLocalContext(localBinders, loweredLeft);
        LevelPointer sourceLevel =
            typeUniverseOf(localBinders, loweredLeft);
        ExpressionPointer loweredGoal = makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality", {sourceLevel}),
                    sourceCarrier),
                loweredLeft),
            loweredRight);
        ExpressionPointer loweredProof = nullptr;
        try {
            loweredProof = autoProveCalcStep(
                localBinders, loweredLeft, loweredRight, sourceCarrier,
                sourceLevel, loweredGoal, line, column);
        } catch (const ElaborateError&) {
        } catch (const TypeError&) {
        }
        if (!loweredProof) debugLine("lowered-fail");
        if (loweredProof) {
            debugLine("lowered-ok");
            ExpressionPointer hopLambda = makeLambda(
                "_cast_z", sourceCarrier,
                makeApplication(makeConstant(leftHop->first),
                                 makeBoundVariable(0)));
            ExpressionPointer lifted = buildEqualityCongruence(
                sourceLevel, sourceCarrier, carrierLevel, carrierType,
                hopLambda, loweredLeft, loweredRight, loweredProof);
            return stitch(lifted);
        }
        return nullptr;
    }

    if (leftNorm.proof || rightNorm.proof) {
        ExpressionPointer retryProof = nullptr;
        try {
            retryProof = autoProveCalcStepRaw(
                localBinders, leftNorm.term, rightNorm.term,
                carrierType, carrierLevel, stepEqualityType,
                line, column);
        } catch (const ElaborateError&) {
        } catch (const TypeError&) {
        }
        if (retryProof) {
            debugLine("retry-ok");
            return stitch(retryProof);
        }
        debugLine("retry-fail");
        return nullptr;
    }
    debugLine("no-move");
    return nullptr;
}

// B3.3b — cast-normalized hypothesis matching, the context-fact half
// of cast normalization: an equality HYPOTHESIS whose statement places
// its casts differently from the goal (`a = ι(1+k)·q + ι r` in scope,
// `a = (ι 1 + ι k)·q + ι r` wanted) matches once both are pushed to
// leaf-cast form; and a hypothesis `ι x = ι y` serves a source-carrier
// sub-goal `x = y` through the hop's `injective` lemma. Called from
// `tryClassifyDiff` after the direct defeq scan declines, at every
// level of the equality battery's diff walk. All terms are in the
// CLOSED (bound-variable) representation throughout — see the
// autoProveClaim convention note at internal.hpp.
ExpressionPointer Elaborator::tryCastNormalizedHypothesisMatch(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer subLeft,
        ExpressionPointer subRight) {
    auto mentionsCoercion = [&](ExpressionPointer term) {
        return containsCoercionConstant(term);
    };
    int binderCount = static_cast<int>(localBinders.size());
    // Sub-diff normal forms, computed on the first cast-bearing
    // hypothesis (most tryClassifyDiff calls never get that far).
    bool subNormalized = false;
    CastNormalForm subLeftNorm{subLeft, nullptr};
    CastNormalForm subRightNorm{subRight, nullptr};
    ExpressionPointer subCarrier;
    LevelPointer subLevel;
    auto ensureSubNormalized = [&]() {
        if (subNormalized) return true;
        try {
            subLeftNorm = castPushToLeaves(subLeft, localBinders);
            subRightNorm = castPushToLeaves(subRight, localBinders);
            subCarrier = inferTypeInLocalContext(localBinders, subLeft);
            subLevel = typeUniverseOf(localBinders, subLeft);
        } catch (const ElaborateError&) {
            return false;
        } catch (const TypeError&) {
            return false;
        }
        subNormalized = true;
        return true;
    };
    // Splice the sub-diff's own normalization proofs around a proof of
    // `subLeftNorm.term = subRightNorm.term`.
    auto wrapSubNormalization = [&](ExpressionPointer core) {
        ExpressionPointer total = core;
        if (subLeftNorm.proof) {
            total = buildEqualityTransitivity(
                subLevel, subCarrier, subLeft, subLeftNorm.term,
                subRightNorm.term, subLeftNorm.proof, total);
        }
        if (subRightNorm.proof) {
            ExpressionPointer reversed = buildEqualitySymmetry(
                subLevel, subCarrier, subRight, subRightNorm.term,
                subRightNorm.proof);
            total = buildEqualityTransitivity(
                subLevel, subCarrier, subLeft, subRightNorm.term,
                subRight, total, reversed);
        }
        return total;
    };
    for (int b = binderCount - 1; b >= 0; --b) {
        if (!mentionsCoercion(localBinders[b].type)) continue;
        autoProveSpend(1);
        ExpressionPointer factType = liftBoundVariables(
            localBinders[b].type, binderCount - b, 0);
        ExpressionPointer factWhnf;
        try {
            factWhnf = weakHeadNormalForm(environment_, factType);
        } catch (const TypeError&) {
            continue;
        }
        // Expect App(App(App(Equality.{lv}, carrier), eqL), eqR).
        auto* app3 = std::get_if<Application>(&factWhnf->node);
        if (!app3) continue;
        auto* app2 = std::get_if<Application>(&app3->function->node);
        if (!app2) continue;
        auto* app1 = std::get_if<Application>(&app2->function->node);
        if (!app1) continue;
        auto* head = std::get_if<Constant>(&app1->function->node);
        if (!head || head->name != "Equality"
            || head->universeArguments.empty()) {
            continue;
        }
        ExpressionPointer factCarrier = app1->argument;
        LevelPointer factLevel = head->universeArguments[0];
        ExpressionPointer eqLeft = app2->argument;
        ExpressionPointer eqRight = app3->argument;
        CastNormalForm eqLeftNorm{eqLeft, nullptr};
        CastNormalForm eqRightNorm{eqRight, nullptr};
        try {
            eqLeftNorm = castPushToLeaves(eqLeft, localBinders);
            eqRightNorm = castPushToLeaves(eqRight, localBinders);
        } catch (const ElaborateError&) {
            continue;
        } catch (const TypeError&) {
            continue;
        }
        if (!ensureSubNormalized()) return nullptr;
        // hypothesisAtNorm : eqLeftNorm.term = eqRightNorm.term.
        auto hypothesisAtNorm = [&]() {
            ExpressionPointer proof =
                makeBoundVariable(binderCount - 1 - b);
            if (eqRightNorm.proof) {
                proof = buildEqualityTransitivity(
                    factLevel, factCarrier, eqLeft, eqRight,
                    eqRightNorm.term, proof, eqRightNorm.proof);
            }
            if (eqLeftNorm.proof) {
                ExpressionPointer reversed = buildEqualitySymmetry(
                    factLevel, factCarrier, eqLeft, eqLeftNorm.term,
                    eqLeftNorm.proof);
                proof = buildEqualityTransitivity(
                    factLevel, factCarrier, eqLeftNorm.term, eqLeft,
                    eqRightNorm.term, reversed, proof);
            }
            return proof;
        };
        // Placement match at the shared leaf-cast normal form.
        if (structurallyEqual(eqLeftNorm.term, subLeftNorm.term)
            && structurallyEqual(eqRightNorm.term, subRightNorm.term)) {
            return wrapSubNormalization(hypothesisAtNorm());
        }
        if (structurallyEqual(eqRightNorm.term, subLeftNorm.term)
            && structurallyEqual(eqLeftNorm.term, subRightNorm.term)) {
            return wrapSubNormalization(buildEqualitySymmetry(
                factLevel, factCarrier, eqLeftNorm.term,
                eqRightNorm.term, hypothesisAtNorm()));
        }
        // Injectivity lowering: a fact `ι x = ι y` serves `x = y` at
        // the hop's source carrier (iterating down a tower, at most
        // the coercion graph's depth).
        ExpressionPointer currentLeft = eqLeftNorm.term;
        ExpressionPointer currentRight = eqRightNorm.term;
        ExpressionPointer currentProof;  // built lazily below
        for (int hopCount = 0; hopCount < 3; ++hopCount) {
            auto* leftApp = std::get_if<Application>(&currentLeft->node);
            auto* rightApp =
                std::get_if<Application>(&currentRight->node);
            if (!leftApp || !rightApp) break;
            auto* leftHead =
                std::get_if<Constant>(&leftApp->function->node);
            auto* rightHead =
                std::get_if<Constant>(&rightApp->function->node);
            if (!leftHead || !rightHead
                || leftHead->name != rightHead->name
                || !isCoercionFunctionName(leftHead->name)) {
                break;
            }
            std::string injectiveName = leftHead->name + ".injective";
            if (environment_.lookup(injectiveName) == nullptr) break;
            ExpressionPointer loweredLeft = leftApp->argument;
            ExpressionPointer loweredRight = rightApp->argument;
            if (!currentProof) currentProof = hypothesisAtNorm();
            currentProof = makeApplication(
                makeApplication(
                    makeApplication(makeConstant(injectiveName),
                                    loweredLeft),
                    loweredRight),
                currentProof);
            currentLeft = loweredLeft;
            currentRight = loweredRight;
            ExpressionPointer loweredCarrier;
            LevelPointer loweredLevel;
            try {
                loweredCarrier = inferTypeInLocalContext(
                    localBinders, currentLeft);
                loweredLevel = typeUniverseOf(localBinders, currentLeft);
            } catch (const ElaborateError&) {
                break;
            } catch (const TypeError&) {
                break;
            }
            if (structurallyEqual(currentLeft, subLeftNorm.term)
                && structurallyEqual(currentRight,
                                     subRightNorm.term)) {
                return wrapSubNormalization(currentProof);
            }
            if (structurallyEqual(currentRight, subLeftNorm.term)
                && structurallyEqual(currentLeft, subRightNorm.term)) {
                return wrapSubNormalization(buildEqualitySymmetry(
                    loweredLevel, loweredCarrier, currentLeft,
                    currentRight, currentProof));
            }
        }
    }
    return nullptr;
}

// B3.2 — the cast-order tier: order goals meet their facts across the
// coercion tower the way B3.1/B3.3 arrange it for equalities. Three
// mechanisms, tried in order:
//   A. PULL-LOWERING — both endpoints factor as ι-images: prove the
//      order at the source carrier (full recursive claim search — the
//      hypotheses live there) and lift through
//      `<hop>.<Rel>_preserves`, transporting the endpoints back along
//      the pull equalities.
//   B. PUSH-RETRY — normalization moved an endpoint: retry the
//      monotonicity/sign machinery and the direct hypothesis scan at
//      the leaf-cast spelling, transporting back.
//   C. REFLECTS-LOWERED FACTS — an order fact at a HIGHER carrier
//      whose sides both pull to the goal's carrier serves the goal
//      through `<hop>.<Rel>_reflects`.
// The recursion terminates: A descends the (acyclic) coercion graph,
// B is guarded on "normalization moved something", C does no search.
ExpressionPointer Elaborator::tryCastOrderTier(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
    OrderJudgment judgment;
    if (!parseOrderJudgment(goalClosed, judgment)) return nullptr;
    // Only the plain two-argument relation shape participates —
    // structure-parameterised relations have no cast story.
    ExpressionPointer rebuilt = makeApplication(
        makeApplication(makeConstant(judgment.relationName),
                        judgment.leftSide),
        judgment.rightSide);
    if (!structurallyEqual(rebuilt, goalClosed)) return nullptr;
    const std::string relSlot =
        judgment.kindTag == "le" ? "LessOrEqual" : "LessThan";
    autoProveSpend(1);
    ExpressionPointer carrier;
    LevelPointer carrierLevel;
    try {
        carrier = inferTypeInLocalContext(localBinders,
                                          judgment.leftSide);
        carrierLevel = typeUniverseOf(localBinders, judgment.leftSide);
    } catch (const ElaborateError&) {
        return nullptr;
    } catch (const TypeError&) {
        return nullptr;
    }
    std::string carrierName = headConstantName(carrier);
    if (carrierName.empty()) return nullptr;
    // Transport a proof of `Rel(fromLeft, fromRight)` to
    // `Rel(toLeft, toRight)` along `toLeft = fromLeft` /
    // `toRight = fromRight` proofs (either may be null = no move),
    // via two one-position `Equality.transport_proposition` steps at
    // `relationCarrier`/`relationLevel`.
    auto transportEndpoints = [&](ExpressionPointer proofAtFrom,
                                  const std::string& relationName,
                                  ExpressionPointer relationCarrier,
                                  LevelPointer relationLevel,
                                  ExpressionPointer fromLeft,
                                  ExpressionPointer fromRight,
                                  ExpressionPointer toLeft,
                                  ExpressionPointer toRight,
                                  ExpressionPointer toLeftEqualsFrom,
                                  ExpressionPointer toRightEqualsFrom) {
        ExpressionPointer proof = proofAtFrom;
        if (toLeftEqualsFrom) {
            // motive z ↦ Rel(z, fromRight), moved from fromLeft to
            // toLeft along sym(toLeftEqualsFrom : toLeft = fromLeft).
            ExpressionPointer motive = makeLambda(
                "_ord_z", relationCarrier,
                makeApplication(
                    makeApplication(
                        makeConstant(relationName),
                        makeBoundVariable(0)),
                    liftBoundVariables(fromRight, 1, 0)));
            ExpressionPointer transported = makeConstant(
                "Equality.transport_proposition", {relationLevel});
            transported = makeApplication(transported, relationCarrier);
            transported = makeApplication(transported, motive);
            transported = makeApplication(transported, fromLeft);
            transported = makeApplication(transported, toLeft);
            transported = makeApplication(
                transported, buildEqualitySymmetry(
                    relationLevel, relationCarrier, toLeft, fromLeft,
                    toLeftEqualsFrom));
            proof = makeApplication(transported, proof);
        }
        if (toRightEqualsFrom) {
            ExpressionPointer motive = makeLambda(
                "_ord_z", relationCarrier,
                makeApplication(
                    makeApplication(
                        makeConstant(relationName),
                        liftBoundVariables(toLeft, 1, 0)),
                    makeBoundVariable(0)));
            ExpressionPointer transported = makeConstant(
                "Equality.transport_proposition", {relationLevel});
            transported = makeApplication(transported, relationCarrier);
            transported = makeApplication(transported, motive);
            transported = makeApplication(transported, fromRight);
            transported = makeApplication(transported, toRight);
            transported = makeApplication(
                transported, buildEqualitySymmetry(
                    relationLevel, relationCarrier, toRight, fromRight,
                    toRightEqualsFrom));
            proof = makeApplication(transported, proof);
        }
        return proof;
    };

    // ---- A: pull-lowering ------------------------------------------
    for (const auto& [registryKey, chain] : environment_.coercionRegistry) {
        if (chain.size() != 1) continue;
        if (std::get<1>(registryKey) != carrierName) continue;
        const std::string& hopName = chain[0];
        const std::string& sourceName = std::get<0>(registryKey);
        std::string preservesName = hopName + "." + relSlot + "_preserves";
        if (environment_.lookup(preservesName) == nullptr) continue;
        std::string sourceRelName = sourceName + "." + relSlot;
        if (environment_.lookup(sourceRelName) == nullptr) continue;
        std::optional<PulledCast> leftPull;
        std::optional<PulledCast> rightPull;
        try {
            leftPull = castPullToRoot(
                judgment.leftSide, hopName, sourceName, carrierName,
                carrier, carrierLevel, localBinders);
            if (leftPull) {
                rightPull = castPullToRoot(
                    judgment.rightSide, hopName, sourceName, carrierName,
                    carrier, carrierLevel, localBinders);
            }
        } catch (const ElaborateError&) {
        } catch (const TypeError&) {
        }
        if (!leftPull || !rightPull) {
            if (castTierDebugEnabled()) {
                std::cerr << "[cast-order]\t" << moduleName_ << ":" << line
                          << "\tpull-fail\thop=" << hopName
                          << " left=" << (leftPull ? 1 : 0) << "\n";
            }
            continue;
        }
        autoProveSpend(2);
        ExpressionPointer loweredGoal = makeApplication(
            makeApplication(makeConstant(sourceRelName),
                            leftPull->source),
            rightPull->source);
        // BOUNDED prover for the lowered goal: hypothesis matches, the
        // indexed order/sign recursions, and a further hop down the
        // tower — deliberately NOT the full claim battery. The tier
        // fires on speculative sub-goals too, and a library scan per
        // speculative lowering blows the effort budget (measured:
        // a sign-split probe `(2:Real) < 0` recursing three carriers
        // deep took Real/division past the budget).
        ExpressionPointer loweredProof;
        try {
            loweredProof = tryLocalFactExactMatch(
                loweredGoal, localBinders);
            if (!loweredProof) {
                Context openedContext =
                    buildContextFromLocalBinders(localBinders);
                ExpressionPointer loweredOpened = openOverLocalBinders(
                    loweredGoal, localBinders, localBinders.size());
                for (int j = static_cast<int>(localBinders.size()) - 1;
                     j >= 0; --j) {
                    ExpressionPointer candidateType = openOverLocalBinders(
                        localBinders[j].type, localBinders, j);
                    bool equal;
                    try {
                        equal = isDefinitionallyEqual(
                            environment_, openedContext, candidateType,
                            loweredOpened);
                    } catch (const TypeError&) {
                        equal = false;
                    }
                    if (equal) {
                        loweredProof = makeBoundVariable(
                            static_cast<int>(localBinders.size()) - 1 - j);
                        break;
                    }
                }
            }
            if (!loweredProof) {
                loweredProof = tryMonotonicityRecursion(
                    loweredGoal, localBinders, 12);
            }
            if (!loweredProof) {
                loweredProof = trySignJudgmentRecursion(
                    loweredGoal, localBinders, 12,
                    /*allowFormBridge=*/true);
            }
            if (!loweredProof) {
                loweredProof = tryCastOrderTier(
                    loweredGoal, localBinders, line);
            }
        } catch (const ElaborateError&) {
        } catch (const TypeError&) {
        }
        if (!loweredProof) {
            if (castTierDebugEnabled()) {
                std::cerr << "[cast-order]\t" << moduleName_ << ":" << line
                          << "\tlowered-claim-fail\thop=" << hopName << "\n";
            }
            continue;
        }
        // preserves(sL, sR, proof) : Rel'(ι sL, ι sR). Verify the
        // lemma's conclusion IS the goal's relation at the coerced
        // endpoints before trusting the lift — a mis-shaped packet
        // lemma must fail the tactic, not the kernel check.
        ExpressionPointer lifted = makeApplication(
            makeApplication(
                makeApplication(makeConstant(preservesName),
                                leftPull->source),
                rightPull->source),
            loweredProof);
        ExpressionPointer coercedLeft = makeApplication(
            makeConstant(hopName), leftPull->source);
        ExpressionPointer coercedRight = makeApplication(
            makeConstant(hopName), rightPull->source);
        ExpressionPointer expected = makeApplication(
            makeApplication(makeConstant(judgment.relationName),
                            coercedLeft),
            coercedRight);
        try {
            ExpressionPointer liftedType = inferTypeInLocalContext(
                localBinders, lifted);
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            if (!isDefinitionallyEqual(
                    environment_, openedContext,
                    openOverLocalBinders(liftedType, localBinders,
                                         localBinders.size()),
                    openOverLocalBinders(expected, localBinders,
                                         localBinders.size()))) {
                if (castTierDebugEnabled()) {
                    std::cerr << "[cast-order]\t" << moduleName_ << ":"
                              << line << "\tlift-shape-mismatch\thop="
                              << hopName << "\n";
                }
                continue;
            }
        } catch (const ElaborateError&) {
            continue;
        } catch (const TypeError&) {
            continue;
        }
        if (castTierDebugEnabled()) {
            std::cerr << "[cast-order]\t" << moduleName_ << ":" << line
                      << "\tpull-lowered-ok\thop=" << hopName << "\n";
        }
        return transportEndpoints(
            lifted, judgment.relationName, carrier, carrierLevel,
            coercedLeft, coercedRight,
            judgment.leftSide, judgment.rightSide,
            leftPull->proof, rightPull->proof);
    }

    // ---- B: push-retry at the leaf-cast spelling --------------------
    if (containsCoercionConstant(goalClosed)) {
        CastNormalForm leftNorm{judgment.leftSide, nullptr};
        CastNormalForm rightNorm{judgment.rightSide, nullptr};
        try {
            leftNorm = castPushToLeaves(judgment.leftSide, localBinders);
            rightNorm = castPushToLeaves(judgment.rightSide, localBinders);
        } catch (const ElaborateError&) {
        } catch (const TypeError&) {
        }
        if (leftNorm.proof || rightNorm.proof) {
            autoProveSpend(1);
            ExpressionPointer normalizedGoal = makeApplication(
                makeApplication(makeConstant(judgment.relationName),
                                leftNorm.term),
                rightNorm.term);
            ExpressionPointer proofAtNormalized;
            // Direct hypothesis at the normalized spelling first (the
            // pre-tactic scans saw only the original form).
            {
                Context openedContext =
                    buildContextFromLocalBinders(localBinders);
                ExpressionPointer normalizedOpened = openOverLocalBinders(
                    normalizedGoal, localBinders, localBinders.size());
                for (int j = static_cast<int>(localBinders.size()) - 1;
                     j >= 0; --j) {
                    ExpressionPointer candidateType = openOverLocalBinders(
                        localBinders[j].type, localBinders, j);
                    bool equal;
                    try {
                        equal = isDefinitionallyEqual(
                            environment_, openedContext, candidateType,
                            normalizedOpened);
                    } catch (const TypeError&) {
                        equal = false;
                    }
                    if (equal) {
                        proofAtNormalized = makeBoundVariable(
                            static_cast<int>(localBinders.size()) - 1 - j);
                        break;
                    }
                }
            }
            if (!proofAtNormalized) {
                proofAtNormalized = tryMonotonicityRecursion(
                    normalizedGoal, localBinders, 12);
            }
            if (!proofAtNormalized) {
                proofAtNormalized = trySignJudgmentRecursion(
                    normalizedGoal, localBinders, 12,
                    /*allowFormBridge=*/true);
            }
            if (proofAtNormalized) {
                return transportEndpoints(
                    proofAtNormalized, judgment.relationName, carrier,
                    carrierLevel, leftNorm.term, rightNorm.term,
                    judgment.leftSide, judgment.rightSide,
                    leftNorm.proof, rightNorm.proof);
            }
        }
    }

    // ---- C: reflects-lowered facts ----------------------------------
    // A fact `Rel_T(L, R)` at a higher carrier whose sides both pull
    // to THIS carrier serves the goal through `<hop>.<Rel>_reflects`.
    {
        int binderCount = static_cast<int>(localBinders.size());
        for (int b = binderCount - 1; b >= 0; --b) {
            if (!containsCoercionConstant(localBinders[b].type)) continue;
            autoProveSpend(1);
            ExpressionPointer factType = liftBoundVariables(
                localBinders[b].type, binderCount - b, 0);
            // Parse the STATED spelling — WHNF would δ-unfold a
            // transparent relation (Integer.LessOrEqual is IsNonneg
            // under the hood) past recognition.
            OrderJudgment fact;
            ExpressionPointer factStated = factType;
            if (!parseOrderJudgment(factStated, fact)) {
                try {
                    factStated = weakHeadNormalForm(
                        environment_, factType);
                } catch (const TypeError&) {
                    continue;
                }
                if (!parseOrderJudgment(factStated, fact)) continue;
            }
            if (fact.kindTag != judgment.kindTag) continue;
            ExpressionPointer factRebuilt = makeApplication(
                makeApplication(makeConstant(fact.relationName),
                                fact.leftSide),
                fact.rightSide);
            if (!structurallyEqual(factRebuilt, factStated)) continue;
            ExpressionPointer factCarrier;
            LevelPointer factLevel;
            try {
                factCarrier = inferTypeInLocalContext(
                    localBinders, fact.leftSide);
                factLevel = typeUniverseOf(localBinders, fact.leftSide);
            } catch (const ElaborateError&) {
                continue;
            } catch (const TypeError&) {
                continue;
            }
            std::string factCarrierName = headConstantName(factCarrier);
            for (const auto& [registryKey, chain]
                     : environment_.coercionRegistry) {
                if (chain.size() != 1) continue;
                if (std::get<0>(registryKey) != carrierName) continue;
                if (std::get<1>(registryKey) != factCarrierName) continue;
                const std::string& hopName = chain[0];
                std::string reflectsName =
                    hopName + "." + relSlot + "_reflects";
                if (environment_.lookup(reflectsName) == nullptr) continue;
                std::optional<PulledCast> leftPull;
                std::optional<PulledCast> rightPull;
                try {
                    leftPull = castPullToRoot(
                        fact.leftSide, hopName, carrierName,
                        factCarrierName, factCarrier, factLevel,
                        localBinders);
                    if (leftPull) {
                        rightPull = castPullToRoot(
                            fact.rightSide, hopName, carrierName,
                            factCarrierName, factCarrier, factLevel,
                            localBinders);
                    }
                } catch (const ElaborateError&) {
                } catch (const TypeError&) {
                }
                if (!leftPull || !rightPull) continue;
                if (!structurallyEqual(leftPull->source,
                                       judgment.leftSide)
                    || !structurallyEqual(rightPull->source,
                                          judgment.rightSide)) {
                    continue;
                }
                // Move the fact to its ι-image spelling (the pull
                // proofs run fact-side = ι(goal-side)), then reflect.
                ExpressionPointer coercedLeft = makeApplication(
                    makeConstant(hopName), leftPull->source);
                ExpressionPointer coercedRight = makeApplication(
                    makeConstant(hopName), rightPull->source);
                ExpressionPointer moved = transportEndpoints(
                    makeBoundVariable(binderCount - 1 - b),
                    fact.relationName, factCarrier, factLevel,
                    fact.leftSide, fact.rightSide,
                    coercedLeft, coercedRight,
                    leftPull->proof ? buildEqualitySymmetry(
                        factLevel, factCarrier, fact.leftSide,
                        coercedLeft, leftPull->proof) : nullptr,
                    rightPull->proof ? buildEqualitySymmetry(
                        factLevel, factCarrier, fact.rightSide,
                        coercedRight, rightPull->proof) : nullptr);
                return makeApplication(
                    makeApplication(
                        makeApplication(makeConstant(reflectsName),
                                        leftPull->source),
                        rightPull->source),
                    moved);
            }
        }
    }
    return nullptr;
}

// Does `term` mention any registered coercion function? Cheap
// syntactic pre-filter shared by the cast tactics.
bool Elaborator::containsCoercionConstant(ExpressionPointer term) const {
    if (!term) return false;
    if (auto* constant = std::get_if<Constant>(&term->node)) {
        return isCoercionFunctionName(constant->name);
    }
    if (auto* application = std::get_if<Application>(&term->node)) {
        return containsCoercionConstant(application->function)
            || containsCoercionConstant(application->argument);
    }
    if (auto* pi = std::get_if<Pi>(&term->node)) {
        return containsCoercionConstant(pi->domain)
            || containsCoercionConstant(pi->codomain);
    }
    if (auto* lambda = std::get_if<Lambda>(&term->node)) {
        return containsCoercionConstant(lambda->domain)
            || containsCoercionConstant(lambda->body);
    }
    if (auto* let = std::get_if<Let>(&term->node)) {
        return containsCoercionConstant(let->type)
            || containsCoercionConstant(let->value)
            || containsCoercionConstant(let->body);
    }
    return false;
}

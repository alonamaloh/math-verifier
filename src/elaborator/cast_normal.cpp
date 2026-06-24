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
    static const std::array<const char*, 3> suffixes{
        "add", "multiply", "subtract"};
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

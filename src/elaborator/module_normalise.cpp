// src/elaborator/module_normalise.cpp
//
// The `module` decision tactic: the free-module / vector-space normaliser.
// Closes an `=` goal over a `VectorSpace.carrier(V)` by normalising both sides
// to a canonical linear combination `Σ cᵢ • vᵢ` — each distinct vector is an
// opaque atom, `•` is distributed over `+`/`−` and pushed through nested
// scales, like vectors are collected by ADDING their field coefficients (the
// coefficient equalities discharged by the `ring` prover), and the canonical
// forms are compared atom-by-atom. If they agree the goal holds, and we emit an
// explicit chain `L = canon = R` built from the vector-space scale/group axioms
// (the kernel rechecks it — the trusted base stays the kernel).
//
// This is strictly stronger than the abelian `group` mode over the same
// carrier, which treats `a • v` as an opaque atom and so cannot collect
// `a • v + b • v` or distribute `a • (u + v)`.

#include "elaborator/internal.hpp"

// The non-throwing core, shared with the calc-step auto-prover. Returns null
// when the tactic does not apply (carrier isn't a vector space, laws absent) or
// the two canonical forms disagree.
ExpressionPointer Elaborator::proveModuleEquality(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType, int line) {
    if (!expectedType) return nullptr;
    expectedType = zetaUnfoldLetBinders(expectedType, localBinders);

    // The goal must be an equality.
    {
        ExpressionPointer goalWhnf =
            weakHeadNormalForm(environment_, expectedType);
        ExpressionPointer head = goalWhnf;
        int depth = 0;
        while (auto* app = std::get_if<Application>(&head->node)) {
            head = app->function;
            ++depth;
        }
        auto* constant = std::get_if<Constant>(&head->node);
        if (!constant || constant->name != "Equality" || depth < 3) {
            return nullptr;
        }
    }
    EqualityComponents goal =
        extractEqualityComponents(expectedType, "module", line);

    size_t binderCount = localBinders.size();
    ExpressionPointer carrierOpened =
        openOverLocalBinders(goal.carrierType, localBinders, binderCount);
    ExpressionPointer leftOpened =
        openOverLocalBinders(goal.leftEndpoint, localBinders, binderCount);
    ExpressionPointer rightOpened =
        openOverLocalBinders(goal.rightEndpoint, localBinders, binderCount);
    LevelPointer level = goal.carrierUniverseLevel;

    // Carrier must be `VectorSpace.carrier(f, V)`.
    ExpressionPointer carrierHead;
    std::vector<ExpressionPointer> carrierArgs;
    peelSpine(carrierOpened, carrierHead, carrierArgs);
    auto* carrierConstant = std::get_if<Constant>(&carrierHead->node);
    if (!carrierConstant || carrierConstant->name != "VectorSpace.carrier"
        || carrierArgs.size() != 2) {
        return nullptr;
    }
    // The scale/group laws the certificate cites must be in scope.
    for (const char* name :
            {"VectorSpace.scale_vector_add", "VectorSpace.scale_scalar_add",
             "VectorSpace.scale_scalar_multiply", "VectorSpace.one_scale",
             "VectorSpace.zero_scale", "VectorSpace.scale_zero",
             "VectorSpace.add_associative", "VectorSpace.add_commutative",
             "VectorSpace.zero_add", "VectorSpace.add_zero"}) {
        if (environment_.lookup(name) == nullptr) return nullptr;
    }

    // CP1 scaffold: the reflexive case (structurally identical sides). The
    // normalise/collect/compare engine is added in the following checkpoints.
    if (structurallyEqual(leftOpened, rightOpened)) {
        ExpressionPointer result =
            buildReflexivity(level, carrierOpened, leftOpened);
        return closeOverLocalBinders(result, localBinders, binderCount);
    }
    return nullptr;
}

ExpressionPointer Elaborator::elaborateModuleNormalise(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType, int line, int column) {
    Frame frame(*this, "module at line " + std::to_string(line),
                localBinders, expectedType, line, column);
    if (!expectedType) {
        throwElaborate(
            "`module` needs an expected type from context — use it in a calc "
            "step or as the body of a theorem with a declared equality "
            "conclusion");
    }
    ExpressionPointer proof = proveModuleEquality(localBinders, expectedType, line);
    if (proof) return proof;
    throwElaborate(
        "`module` could not close this goal. It proves `=` goals over a "
        "`VectorSpace.carrier(V)` by normalising both sides to a canonical "
        "`Σ cᵢ • vᵢ` (distributing `•`, collecting like vectors by adding "
        "coefficients) — check the goal is such a rearrangement and the "
        "vector-space laws are in scope.");
}

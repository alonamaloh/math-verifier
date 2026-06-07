#pragma once

// Pure term-surgery utilities used throughout the elaborator: de Bruijn
// abstraction, opening/closing over the local-binder context, and
// free-variable / bound-variable queries.
//
// These are FREE FUNCTIONS: they touch no Elaborator state. Most are pure
// term surgery (no environment at all); a few read-only queries take the
// kernel `Environment` explicitly (e.g. headConstantName, which weak-head-
// normalises). They operate solely on their arguments plus the kernel's own
// free functions (shift, structurallyEqual, weakHeadNormalForm, open/
// closeBinder, make*). Extracted from the Elaborator class so they stand
// alone, are independently testable, and don't drag the class's state into
// scope. Call sites are unchanged — the unqualified calls bind to these once
// the (identically signed) members were removed, or via a thin forwarding
// member for the env-taking ones.

#include "kernel/expression.hpp"
#include "kernel/kernel.hpp"
#include "kernel/level.hpp"

#include <cstdint>
#include <map>
#include <string>
#include <vector>

// One local binder in the elaborator's context. Tracks the user-visible
// name and the kernel type. Used both to compute de Bruijn indices for
// name lookup and to construct a kernel Context for inferType calls
// during `=` desugaring and `congruenceOf(...)` elaboration.
//
// `value` is non-null for let-style binders (surface `let X := V`). It
// flows through to ContextEntry.value when the elaborator builds an
// opened Context for kernel calls — so isDefinitionallyEqual can ζ
// the let-name during equality checks. The auto-prover separately
// uses it to ζ-unfold at the closed-term level for structural
// matchers (lemma index, hypothesis match).
struct LocalBinder {
    std::string name;
    ExpressionPointer type;
    ExpressionPointer value = nullptr;
};

// Returns the FreeVariable name used when opening / closing the binder
// at `localBinders[index]` (Internal origin). Wildcards (`_`) get a
// position-dependent suffix so multiple `_` binders in the same stack
// don't collapse to the same FreeVariable. Every site that opens an
// Internal-origin FV for a local binder OR constructs a Context entry
// for one MUST go through this helper — otherwise opens and closes get
// out of sync (`closeBinder` searches by literal name) and inferType
// fails to find type info for the FV in its context. The user-visible
// binder name in `localBinders[i].name` stays unchanged; only the FV
// naming is rewritten here.
inline std::string openingNameFor(
    const std::vector<LocalBinder>& localBinders, size_t index) {
    const std::string& original = localBinders[index].name;
    if (original == "_") {
        return "_wildcard_" + std::to_string(index);
    }
    // Disambiguate against earlier binders with the same name —
    // FreeVariables are identified by (name, origin), so two binders
    // sharing a name would collide as a single FV, breaking
    // substitution and unification. The inner binder (higher index)
    // shadows the outer in the user's view, so it's the inner that
    // gets the unique suffix.
    for (size_t earlier = 0; earlier < index; ++earlier) {
        if (localBinders[earlier].name == original) {
            return original + "_shadow_" + std::to_string(index);
        }
    }
    return original;
}

// ---- read-only Environment queries (defs in .cpp) ----

// The head constant name of a (possibly applied, possibly redex) type:
// strip Application spines; if that doesn't reach a Constant, weak-head-
// normalise and strip again. Returns "<unknown>" if there is no Constant
// head. Free over the kernel Environment (the elaborator keeps a thin
// forwarding member so its many call sites stay `headConstantName(t)`).
std::string headConstantName(const Environment& environment,
                             ExpressionPointer typeExpression);

// ---- de Bruijn / local-binder term utilities (defs in .cpp) ----

ExpressionPointer abstractOverBoundVariables(
    ExpressionPointer expression,
    const std::vector<int>& indices);

ExpressionPointer abstractOverBoundVariable(
    ExpressionPointer expression,
    int targetIndex,
    int currentDepth = 0);

ExpressionPointer openOverLocalBinders(
    ExpressionPointer term,
    const std::vector<LocalBinder>& localBinders,
    size_t count);

ExpressionPointer closeOverLocalBinders(
    ExpressionPointer term,
    const std::vector<LocalBinder>& localBinders,
    size_t count);

// The Internal-origin FreeVariable that openOverLocalBinders substitutes for
// localBinders[index] — i.e. how that binder appears in opened terms. Lets
// callers construct a reference to a specific in-scope binder (e.g. as a
// candidate argument) that is recognised by the opened forms of types/goals.
ExpressionPointer openedLocalBinderReference(
    const std::vector<LocalBinder>& localBinders, size_t index);

bool referencesBoundBelowThreshold(ExpressionPointer expression,
                                    int threshold,
                                    int currentDepth = 0);

bool containsFreeVariable(const ExpressionPointer& expression);

ExpressionPointer abstractStructuralOccurrenceMasked(
    ExpressionPointer expression,
    ExpressionPointer target,
    int currentDepth,
    int& positionCounter,
    uint32_t mask);

ExpressionPointer abstractStructuralOccurrence(
    ExpressionPointer expression,
    ExpressionPointer target,
    int currentDepth,
    int& occurrenceCount);


// ---- more pure term helpers (defs in .cpp) ----

ExpressionPointer liftBoundVariables(
    ExpressionPointer expression, int increment, int threshold);

int countLeadingPis(ExpressionPointer type);

size_t countExpressionNodes(ExpressionPointer e);

std::string applicationHeadConstantName(
    ExpressionPointer expression);

ExpressionPointer zetaUnfoldLetBinders(
    ExpressionPointer expression,
    const std::vector<LocalBinder>& localBinders,
    int currentDepth);

Context buildContextFromLocalBinders(
    const std::vector<LocalBinder>& localBinders);

ExpressionPointer substituteBoundVariable(
    ExpressionPointer body, ExpressionPointer argument, int target);


// ---- let-binder zeta-unfolding + free-variable substitution ----

ExpressionPointer zetaUnfoldLetBinders(
    ExpressionPointer term,
    const std::vector<LocalBinder>& localBinders);

ExpressionPointer substituteFreeVariables(
    ExpressionPointer expression,
    const std::map<std::string, ExpressionPointer>& assignment,
    int binderDepth = 0);


// ---- generic Equality proof-term builders ----

ExpressionPointer buildEqualityTransitivity( LevelPointer universeLevel, ExpressionPointer carrierType, ExpressionPointer A, ExpressionPointer B, ExpressionPointer C, ExpressionPointer p1, ExpressionPointer p2);

ExpressionPointer buildEqualitySymmetry( LevelPointer universeLevel, ExpressionPointer carrierType, ExpressionPointer A, ExpressionPointer B, ExpressionPointer p);

ExpressionPointer buildEqualityCongruenceSameCarrier( LevelPointer universeLevel, ExpressionPointer carrierType, ExpressionPointer lambda, ExpressionPointer x, ExpressionPointer y, ExpressionPointer p);

ExpressionPointer buildEqualityCongruence( LevelPointer sourceUniverseLevel, ExpressionPointer sourceCarrierType, LevelPointer targetUniverseLevel, ExpressionPointer targetCarrierType, ExpressionPointer lambda, ExpressionPointer x, ExpressionPointer y, ExpressionPointer p);

ExpressionPointer buildReflexivity( LevelPointer universeLevel, ExpressionPointer carrierType, ExpressionPointer x);

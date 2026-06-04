#pragma once

// Pure term-surgery utilities used throughout the elaborator: de Bruijn
// abstraction, opening/closing over the local-binder context, and
// free-variable / bound-variable queries.
//
// These are FREE FUNCTIONS: they touch no Elaborator state (not even the
// environment). They operate solely on their arguments plus the kernel's
// own free functions (shift, structurallyEqual, open/closeBinder, make*).
// Extracted from the Elaborator class so they stand alone, are independently
// testable, and don't drag the class's state into scope. Call sites are
// unchanged — the unqualified calls bind to these once the (identically
// signed) members were removed.

#include "expression.hpp"
#include "kernel.hpp"
#include "level.hpp"

#include <cstdint>
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


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
#include <functional>
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
    // True when `type` is a Proposition, i.e. `value` is a PROOF term
    // (`claim X : T by V` / `calc … as X`). Proof values are omitted from
    // the kernel ContextEntry: ζ-substituting a proof into the terms of a
    // defeq query can never decide a type-level equality, but it makes
    // every isDefinitionallyEqual under the binder pay an O(proof-size)
    // substitution walk on both sides (and bloats the defeq cache keys) —
    // a measured 120× blowup on proof-heavy calc blocks. The auto-prover's
    // closed-term matchers still see `value` via the LocalBinder itself.
    bool valueIsProof = false;
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

// Constant-name equality modulo the Natural constructor wrappers
// (PLAN_NATURAL_SEALING): the bare alias-typed `zero`/`successor` and
// the raw `Natural.Raw.zero`/`Natural.Raw.successor` denote the same
// value up to a transparent δ, so structural matchers — whose pattern
// side comes from statements (wrapper spelling) while the subject side
// may be weak-head-normalised (raw spelling) — compare through this.
inline bool constantNamesMatchModuloNaturalWrapper(
        const std::string& left, const std::string& right) {
    if (left == right) return true;
    auto canonical = [](const std::string& name) -> const std::string& {
        static const std::string successorWrapper = "successor";
        static const std::string zeroWrapper = "zero";
        if (name == "Natural.Raw.successor") return successorWrapper;
        if (name == "Natural.Raw.zero") return zeroWrapper;
        return name;
    };
    return canonical(left) == canonical(right);
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

// An optional extra notion of "this subterm IS the rewrite target" layered
// on top of plain `structurallyEqual` during the occurrence search. The
// occurrence walker is purely structural, so two definitionally-equal but
// syntactically-distinct forms of the same endpoint — most importantly a
// numeral written one way (`(1 : Rational)` ⤳ `Rational.one`) versus the
// same numeral reached through a coercion tower (`Natural.to_rational(1)`,
// which an OPAQUE quotient like Rational cannot WHNF-reduce to `Rational.one`)
// — would not be recognised as occurrences. The citation matcher already
// bridges these via `asNumeralLiteral`; supplying that same bridge here lets
// `by substituting` see them too. `nullptr` (the default) means structural-
// only, exactly as before.
using StructuralNodeMatcher =
    std::function<bool(const ExpressionPointer&, const ExpressionPointer&)>;

ExpressionPointer abstractStructuralOccurrenceMasked(
    ExpressionPointer expression,
    ExpressionPointer target,
    int currentDepth,
    int& positionCounter,
    uint32_t mask,
    const StructuralNodeMatcher* nodeMatches = nullptr);

ExpressionPointer abstractStructuralOccurrence(
    ExpressionPointer expression,
    ExpressionPointer target,
    int currentDepth,
    int& occurrenceCount,
    const StructuralNodeMatcher* nodeMatches = nullptr);


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

// Replace every occurrence of BoundVariable(target) with `replacement`,
// WITHOUT removing a binder: all other indices stay as they are (unlike
// substituteBoundVariable, which β-reduces a binder away and shifts).
ExpressionPointer replaceBoundVariableInPlace(
    ExpressionPointer body, int target, ExpressionPointer replacement);


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

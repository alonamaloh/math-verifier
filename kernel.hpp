#pragma once

#include "expression.hpp"

#include <map>
#include <stdexcept>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

struct TypeError : std::runtime_error {
    using std::runtime_error::runtime_error;

    // Optional structured info. The kernel populates these for the
    // type-mismatch case (Application argument vs Pi domain, Let value
    // vs declared type, etc.) so callers can paraphrase the error
    // with pretty-printed types rather than the bare message. They
    // are `nullptr` when the error has no meaningful "expected/actual"
    // pair (e.g. "internal" errors, name-collision errors).
    ExpressionPointer expectedType;
    ExpressionPointer actualType;
};

struct ContextEntry {
    std::string name;
    ExpressionPointer type;
    FreeVariableOrigin origin = FreeVariableOrigin::User;
};
using Context = std::vector<ContextEntry>;

// A global declaration is one of:
//   Axiom       — a name and its type, no body ("assume this exists").
//   Definition  — name, declared type, and body whose inferred type matches.
//                 Delta-reduces to body in weakHeadNormalForm.
//   Inductive   — an inductively-defined type, with its kind (Sort i for v1,
//                 since we don't yet support parameters or indices) and
//                 the names of its constructors. Stuck under reduction.
//   Constructor — a single constructor of an inductive type, with the name
//                 of that inductive, the constructor's index within it,
//                 and the constructor's declared type. Stuck.
//   Recursor    — the auto-generated eliminator for an inductive. Stuck on
//                 its own, but iota-reduces when fully applied with the
//                 final argument being a constructor application.
// Each declaration carries the universe parameter names it abstracts over.
// At a Constant use site, the caller supplies a matching list of Level
// arguments; inferType substitutes those into the declaration's type.
// Most declarations in everyday use have no parameters (empty vector).
struct Axiom       { std::vector<std::string> universeParameters;
                     ExpressionPointer type; };
struct Definition  { std::vector<std::string> universeParameters;
                     ExpressionPointer type; ExpressionPointer body; };
// An Inductive's `kind` is a Pi-chain ending in a Sort. The first
// `numParameters` Pis bind parameters (uniform across constructors); the
// remaining Pis bind indices (allowed to vary per constructor). For
// non-parameterised, non-indexed inductives like Natural, the kind is a
// plain Sort and numParameters is 0.
struct Inductive   { std::vector<std::string> universeParameters;
                     ExpressionPointer kind;
                     std::vector<std::string> constructorNames;
                     int numParameters; };
struct Constructor { std::vector<std::string> universeParameters;
                     std::string inductiveName;
                     int constructorIndex;
                     ExpressionPointer type; };
struct Recursor    { std::vector<std::string> universeParameters;
                     std::string inductiveName;
                     ExpressionPointer type;
                     int numConstructors;
                     int numParameters;
                     int numIndices; };

using Declaration = std::variant<Axiom, Definition,
                                 Inductive, Constructor, Recursor>;

struct Environment {
    std::map<std::string, Declaration> declarations;
    // Elaborator-side metadata: number of leading implicit binders for
    // each declaration. The kernel itself ignores this — it's used by
    // the surface elaborator to decide which leading arguments at a
    // call site to fill in via unification. A declaration not present
    // in this map has zero implicit binders. Phase 2.1 restricts
    // implicit binders to leading consecutive positions.
    std::map<std::string, int> implicitArgumentCounts;

    // Operator-dispatch registry. Key: (operator symbol, left operand
    // type head name, right operand type head name). Value: the fully-
    // qualified function name to dispatch to. Populated by `operator
    // (<sym>) on (<T1>, <T2>) := <F>;` declarations. The kernel itself
    // never reads this — it's a surface-elaborator concern.
    std::map<std::tuple<std::string, std::string, std::string>,
              std::string> operatorRegistry;

    // Function-name overload aliases. Key: the surface alias name (e.g.
    // "add"). Value: a list of fully-qualified function names that the
    // alias resolves to. The elaborator picks one by matching argument
    // types at each call site. Populated by `overload <alias> := <F>;`.
    std::map<std::string, std::vector<std::string>> overloadAliases;

    // Coercion registry. Key: (sourceTypeName, targetTypeName). Value:
    // the chain of fully-qualified function names to compose, in order
    // (apply functionNames[0] first, then functionNames[1], etc.). A
    // direct registration is a one-element chain; transitive entries
    // computed at registration time have more. Used by the ascription
    // path to insert coercion calls when `(expr : T)` has expr of a
    // different source type with a registered embedding.
    std::map<std::tuple<std::string, std::string>,
              std::vector<std::string>> coercionRegistry;

    const Declaration* lookup(const std::string& name) const {
        auto iterator = declarations.find(name);
        return iterator == declarations.end() ? nullptr : &iterator->second;
    }

    int implicitArgumentCount(const std::string& name) const {
        auto iterator = implicitArgumentCounts.find(name);
        return iterator == implicitArgumentCounts.end()
            ? 0 : iterator->second;
    }

    // Look up a registered operator-dispatch target. Returns the
    // function name on success, empty string if no registration exists
    // for that (operator, leftType, rightType) triple.
    std::string lookupOperator(
        const std::string& operatorSymbol,
        const std::string& leftTypeName,
        const std::string& rightTypeName) const {
        auto iterator = operatorRegistry.find(
            std::make_tuple(operatorSymbol, leftTypeName, rightTypeName));
        return iterator == operatorRegistry.end()
            ? std::string{} : iterator->second;
    }

    // Look up the list of fully-qualified function names registered
    // under `aliasName`. Returns an empty vector if the alias is
    // unknown. Callers do overload resolution by matching argument
    // types against each candidate's signature.
    const std::vector<std::string>* lookupOverloads(
        const std::string& aliasName) const {
        auto iterator = overloadAliases.find(aliasName);
        return iterator == overloadAliases.end()
            ? nullptr : &iterator->second;
    }
};

// Type-checks `declaredType` (it must itself be a type) and adds an axiom
// to `environment`. Throws TypeError on name collision or ill-formed type.
// `universeParameters` are the names of the level parameters this axiom
// abstracts over; pass {} for a non-polymorphic axiom.
void addAxiom(Environment& environment, std::string name,
              std::vector<std::string> universeParameters,
              ExpressionPointer declaredType);

inline void addAxiom(Environment& environment, std::string name,
                     ExpressionPointer declaredType) {
    addAxiom(environment, std::move(name), {}, std::move(declaredType));
}

// Type-checks both `declaredType` and `body`, requires they agree
// definitionally, and adds the definition to `environment`.
void addDefinition(Environment& environment, std::string name,
                   std::vector<std::string> universeParameters,
                   ExpressionPointer declaredType, ExpressionPointer body);

inline void addDefinition(Environment& environment, std::string name,
                          ExpressionPointer declaredType,
                          ExpressionPointer body) {
    addDefinition(environment, std::move(name), {},
                  std::move(declaredType), std::move(body));
}

// A constructor specification supplied to addInductive: the constructor's
// name and its declared type (a Pi-prefix ending in the inductive being
// declared).
struct ConstructorSpec {
    std::string name;
    ExpressionPointer type;
};

// Declares an inductive type and atomically adds: the inductive itself,
// each of its constructors, and an automatically-generated recursor under
// the name "<inductiveName>_recursor". For v1, the `kind` must be a plain
// Sort (no parameters or indices), and constructor types must be a Pi-
// prefix whose recursive arguments are direct references to the inductive
// (no nested or higher-order recursion). Strict positivity is the user's
// responsibility; the kernel does not check it yet.
// Canonical signature: inductive with explicit numParameters. The kind is
// a Pi-chain Π(p_1) ... Π(p_n). Π(i_1) ... Π(i_m). Sort u, where the first
// `numParameters` Pis bind parameters and the remaining Pis bind indices.
// Each constructor's type must begin with those same parameter Pis and
// end in `inductiveName` applied to the parameters and to some specific
// indices.
void addInductive(Environment& environment, std::string inductiveName,
                  std::vector<std::string> universeParameters,
                  ExpressionPointer kind,
                  int numParameters,
                  std::vector<ConstructorSpec> constructors);

// Convenience overloads for the most common cases. Without numParameters,
// the inductive has zero parameters and the kind must be a plain Sort.
inline void addInductive(Environment& environment, std::string inductiveName,
                         std::vector<std::string> universeParameters,
                         ExpressionPointer kind,
                         std::vector<ConstructorSpec> constructors) {
    addInductive(environment, std::move(inductiveName),
                 std::move(universeParameters),
                 std::move(kind), 0, std::move(constructors));
}
inline void addInductive(Environment& environment, std::string inductiveName,
                         ExpressionPointer kind,
                         std::vector<ConstructorSpec> constructors) {
    addInductive(environment, std::move(inductiveName), {},
                 std::move(kind), 0, std::move(constructors));
}
inline void addInductive(Environment& environment, std::string inductiveName,
                         ExpressionPointer kind,
                         int numParameters,
                         std::vector<ConstructorSpec> constructors) {
    addInductive(environment, std::move(inductiveName), {},
                 std::move(kind), numParameters, std::move(constructors));
}

// Adds `amount` to every BoundVariable whose index is at least `cutoff`.
// Used to keep indices coherent when a term crosses additional binders.
ExpressionPointer shift(ExpressionPointer expression, int amount, int cutoff = 0);

// Cheap allocation-free structural equality (alpha-equivalent via
// de Bruijn). Returns true only on truly identical terms — does not
// perform any reductions. Pointer-identity short-circuits at every
// level. Used by `isDefinitionallyEqual` as a fast path and by the
// elaborator's `rewrite` tactic to locate the unique occurrence of
// the lemma's left endpoint inside the goal's left side.
bool structurallyEqual(ExpressionPointer left, ExpressionPointer right);

// Walks `expression` and replaces every LevelParam appearing in any Sort
// or Constant universe-argument list, mapping each name in `parameterNames`
// to the corresponding entry in `replacements`. Used to instantiate a
// polymorphic constant when its universe arguments are known.
ExpressionPointer substituteUniverseLevels(
    ExpressionPointer expression,
    const std::vector<std::string>& parameterNames,
    const std::vector<LevelPointer>& replacements);

// Replaces BoundVariable{targetIndex} with `replacement` and decrements
// higher indices (the binder being removed). Recurses under binders with
// targetIndex+1 and a shifted replacement. Used by beta reduction.
ExpressionPointer substitute(ExpressionPointer expression,
                         int targetIndex,
                         ExpressionPointer replacement);

// Replaces BoundVariable{0} with the supplied free variable and decrements
// higher indices. Used to descend under a binder while exposing the bound
// variable as a free variable for type-checking and equality. The `origin`
// argument distinguishes user-supplied fresh names (the default) from
// kernel-internal ones used by isDefinitionallyEqual and the recursor
// builders.
ExpressionPointer openBinder(ExpressionPointer expression,
                             const std::string& freshName,
                             FreeVariableOrigin origin
                                 = FreeVariableOrigin::User);

// Replaces every FreeVariable matching (name, origin) with a BoundVariable
// referring to a binder added one level above `expression`, and shifts
// other bound variables up by one. The inverse of openBinder.
ExpressionPointer closeBinder(ExpressionPointer expression,
                              const std::string& name,
                              FreeVariableOrigin origin
                                  = FreeVariableOrigin::User);

// Default fuel for kernel functions that recursively reduce. The fuel is
// decremented at every reduction step and recursive call; functions throw
// (or return false conservatively) when it runs out. This guards against
// non-termination for malformed input — a well-typed expression in our
// fragment never approaches this bound for any realistic input.
constexpr int defaultFuel = 10000;

// Optional runtime invariant checks. When true, inferType performs a
// kind-soundness postcondition on every successful inference (it re-infers
// the result type and requires it to be a Sort). This roughly doubles the
// cost of type-checking but catches the entire class of "kernel produced
// internally-inconsistent output" bugs. Off by default; tests enable it.
extern bool kernelCheckInvariants;

// Reduces only the head: enough to see whether the outermost form is a
// Sort, Pi, Lambda, etc. Unfolds definitions in head position
// (delta-reduction). Throws TypeError on fuel exhaustion.
ExpressionPointer weakHeadNormalForm(const Environment& environment,
                                 ExpressionPointer expression,
                                 int fuel = defaultFuel);

// Definitional equality: same up to reduction, alpha-renaming, η, and
// proof irrelevance. The `context` is consulted when proof irrelevance
// needs to infer the types of the two sides. Returns false conservatively
// when fuel runs out.
bool isDefinitionallyEqual(const Environment& environment,
                           const Context& context,
                           ExpressionPointer left,
                           ExpressionPointer right,
                           int fuel = defaultFuel);

// Universe cumulativity: returns true if `subType` can be used wherever
// `superType` is expected. Equivalent to isDefinitionallyEqual except at
// the Sort head, where Sort m <: Sort n whenever m <= n; and at the Pi
// head, where the domains must be equal but the codomains may be related
// by subtyping (covariant codomain). Used in Application argument checks,
// addDefinition body checks, and Let value checks. Returns false on
// fuel exhaustion.
bool isSubtype(const Environment& environment,
               const Context& context,
               ExpressionPointer subType,
               ExpressionPointer superType,
               int fuel = defaultFuel);

// Returns the type of `expression` in `environment` and `context`,
// or throws TypeError.
ExpressionPointer inferType(const Environment& environment,
                        const Context& context,
                        ExpressionPointer expression);

// Returns a name not present in `context`. Tries `displayHint` first,
// then "displayHint_1", "displayHint_2", ...
std::string freshName(const std::string& displayHint, const Context& context);

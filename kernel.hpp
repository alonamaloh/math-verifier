#pragma once

#include "expression.hpp"

#include <map>
#include <stdexcept>
#include <string>
#include <variant>
#include <vector>

struct TypeError : std::runtime_error {
    using std::runtime_error::runtime_error;
};

struct ContextEntry {
    std::string name;
    ExpressionPointer type;
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
struct Inductive   { std::vector<std::string> universeParameters;
                     ExpressionPointer kind;
                     std::vector<std::string> constructorNames; };
struct Constructor { std::vector<std::string> universeParameters;
                     std::string inductiveName;
                     int constructorIndex;
                     ExpressionPointer type; };
struct Recursor    { std::vector<std::string> universeParameters;
                     std::string inductiveName;
                     ExpressionPointer type;
                     int numConstructors; };

using Declaration = std::variant<Axiom, Definition,
                                 Inductive, Constructor, Recursor>;

struct Environment {
    std::map<std::string, Declaration> declarations;

    const Declaration* lookup(const std::string& name) const {
        auto iterator = declarations.find(name);
        return iterator == declarations.end() ? nullptr : &iterator->second;
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
void addInductive(Environment& environment, std::string inductiveName,
                  std::vector<std::string> universeParameters,
                  ExpressionPointer kind,
                  std::vector<ConstructorSpec> constructors);

inline void addInductive(Environment& environment, std::string inductiveName,
                         ExpressionPointer kind,
                         std::vector<ConstructorSpec> constructors) {
    addInductive(environment, std::move(inductiveName), {},
                 std::move(kind), std::move(constructors));
}

// Adds `amount` to every BoundVariable whose index is at least `cutoff`.
// Used to keep indices coherent when a term crosses additional binders.
ExpressionPointer shift(ExpressionPointer expression, int amount, int cutoff = 0);

// Replaces BoundVariable{targetIndex} with `replacement` and decrements
// higher indices (the binder being removed). Recurses under binders with
// targetIndex+1 and a shifted replacement. Used by beta reduction.
ExpressionPointer substitute(ExpressionPointer expression,
                         int targetIndex,
                         ExpressionPointer replacement);

// Replaces BoundVariable{0} with FreeVariable{freshName} and decrements
// higher indices. Used to descend under a binder while exposing the bound
// variable as a free variable for type-checking and equality.
ExpressionPointer openBinder(ExpressionPointer expression,
                         const std::string& freshName);

// Replaces FreeVariable{name} with a BoundVariable referring to a binder
// added one level above `expression`, and shifts other bound variables up
// by one. Used by inferType on Lambda to rebuild the Pi.
ExpressionPointer closeBinder(ExpressionPointer expression, const std::string& name);

// Reduces only the head: enough to see whether the outermost form is a
// Sort, Pi, Lambda, etc. Unfolds definitions in head position
// (delta-reduction).
ExpressionPointer weakHeadNormalForm(const Environment& environment,
                                 ExpressionPointer expression);

// Definitional equality: same up to reduction, alpha-renaming, η, and
// proof irrelevance. The `context` is consulted when proof irrelevance
// needs to infer the types of the two sides.
bool isDefinitionallyEqual(const Environment& environment,
                           const Context& context,
                           ExpressionPointer left,
                           ExpressionPointer right);

// Universe cumulativity: returns true if `subType` can be used wherever
// `superType` is expected. Equivalent to isDefinitionallyEqual except at
// the Sort head, where Sort m <: Sort n whenever m <= n; and at the Pi
// head, where the domains must be equal but the codomains may be related
// by subtyping (covariant codomain). Used in Application argument checks,
// addDefinition body checks, and Let value checks.
bool isSubtype(const Environment& environment,
               const Context& context,
               ExpressionPointer subType,
               ExpressionPointer superType);

// Returns the type of `expression` in `environment` and `context`,
// or throws TypeError.
ExpressionPointer inferType(const Environment& environment,
                        const Context& context,
                        ExpressionPointer expression);

// Returns a name not present in `context`. Tries `displayHint` first,
// then "displayHint_1", "displayHint_2", ...
std::string freshName(const std::string& displayHint, const Context& context);

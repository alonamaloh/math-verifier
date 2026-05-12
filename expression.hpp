#pragma once

#include "level.hpp"

#include <memory>
#include <string>
#include <type_traits>
#include <variant>
#include <vector>

struct Expression;
using ExpressionPointer = std::shared_ptr<Expression>;

// Distinguishes free variables introduced by the user (via makeFreeVariable
// and ContextEntry) from those introduced by the kernel internally — for
// example, the placeholder names used by isDefinitionallyEqual when it
// opens a Pi/Lambda binder for structural comparison, or the placeholders
// used by buildCaseType / buildRecursorType during recursor construction.
// Two FreeVariables are identified by *both* their name and their origin,
// so the kernel's internal names cannot collide with anything the user can
// construct.
enum class FreeVariableOrigin { User, Internal };

struct BoundVariable { int deBruijnIndex; };
struct FreeVariable  { std::string name;
                       FreeVariableOrigin origin = FreeVariableOrigin::User; };
struct Sort          { LevelPointer level; };
struct Pi            { std::string displayHint; ExpressionPointer domain; ExpressionPointer codomain; };
struct Lambda        { std::string displayHint; ExpressionPointer domain; ExpressionPointer body; };
struct Application   { ExpressionPointer function; ExpressionPointer argument; };
struct Constant      { std::string name;
                       std::vector<LevelPointer> universeArguments; };
struct Let           { std::string displayHint;
                       ExpressionPointer type;
                       ExpressionPointer value;
                       ExpressionPointer body; };

struct Expression {
    std::variant<BoundVariable, FreeVariable, Sort, Pi, Lambda, Application, Constant, Let> node;

    Expression() = default;

    template <typename Alternative,
              typename = std::enable_if_t<
                  !std::is_same_v<std::decay_t<Alternative>, Expression>>>
    Expression(Alternative&& alternative)
        : node(std::forward<Alternative>(alternative)) {}
};

inline ExpressionPointer makeBoundVariable(int index) {
    return std::make_shared<Expression>(BoundVariable{index});
}
inline ExpressionPointer makeFreeVariable(std::string name) {
    return std::make_shared<Expression>(FreeVariable{std::move(name)});
}
// Note: no public builder exists for Internal-origin FreeVariables — they
// are an implementation detail of the kernel (isDefinitionallyEqual binder
// opening, buildCaseType/buildRecursorType placeholders) and the User
// origin is the only one client code should construct.
// Sort taking a level expression. Universe-polymorphic code passes a Level
// containing a LevelParam; concrete code uses LevelConst (via the int
// overload below). Level 0 is Proposition; level n+1 is "Type n".
inline ExpressionPointer makeSort(LevelPointer level) {
    return std::make_shared<Expression>(Sort{std::move(level)});
}
inline ExpressionPointer makeSort(int rawLevel) {
    return makeSort(makeLevelConst(rawLevel));
}
inline ExpressionPointer makeProposition() {
    return makeSort(0);
}
inline ExpressionPointer makeType(int index) {
    return makeSort(index + 1);
}
// Polymorphic Type universe: `Type u` lives at Sort (u+1).
inline ExpressionPointer makeType(LevelPointer level) {
    return makeSort(makeLevelSuccessor(std::move(level)));
}
inline ExpressionPointer makePi(std::string displayHint,
                            ExpressionPointer domain,
                            ExpressionPointer codomain) {
    return std::make_shared<Expression>(
        Pi{std::move(displayHint), std::move(domain), std::move(codomain)});
}
inline ExpressionPointer makeLambda(std::string displayHint,
                                ExpressionPointer domain,
                                ExpressionPointer body) {
    return std::make_shared<Expression>(
        Lambda{std::move(displayHint), std::move(domain), std::move(body)});
}
inline ExpressionPointer makeApplication(ExpressionPointer function,
                                     ExpressionPointer argument) {
    return std::make_shared<Expression>(
        Application{std::move(function), std::move(argument)});
}
inline ExpressionPointer makeConstant(std::string name) {
    return std::make_shared<Expression>(Constant{std::move(name), {}});
}
inline ExpressionPointer makeConstant(std::string name,
                                      std::vector<LevelPointer> universeArguments) {
    return std::make_shared<Expression>(
        Constant{std::move(name), std::move(universeArguments)});
}
inline ExpressionPointer makeLet(std::string displayHint,
                                 ExpressionPointer type,
                                 ExpressionPointer value,
                                 ExpressionPointer body) {
    return std::make_shared<Expression>(
        Let{std::move(displayHint), std::move(type),
            std::move(value), std::move(body)});
}
